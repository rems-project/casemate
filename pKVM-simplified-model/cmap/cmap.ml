module ZMap = Map.Make (Z)

type 'a cache = (Z.t * 'a option array) list

type 'a t = {
  mutable c : 'a cache;
  map : 'a option array ZMap.t;
  (* Those two counters ensures that this imperative implementation
     behaves like a functional implementation by updating a counter
     on the callee object, so that if it is reused, only the imperative
     counter will be incremented leading to an assertion fail. *)
  fn_count : int;
  mutable imp_count : int;
}

let cache_size = 2
let empty () = { c = []; map = ZMap.empty; fn_count = 0; imp_count = 0 }
let map_bits x = Z.shift_right x 12
let array_bits x = Z.(to_int (shift_right (logand x (of_int 0xfff)) 3))

let rec lookup_cache addr : 'a cache -> 'b = function
  | [] -> None
  | (a, t) :: _ when a = addr -> Some t
  | _ :: q -> lookup_cache addr q

let rec is_cached x i : 'a cache -> 'a cache = function
  | [] -> []
  | _ when i = 0 -> []
  | (a, _) :: q when a = x -> q
  | t :: q -> t :: is_cached x (i - 1) q

let add_to_cache addr line (cache : 'a cache) =
  (addr, line) :: is_cached addr cache_size cache

let rec insert x va map =
  assert (map.fn_count = map.imp_count);
  try
    let ad = map_bits x in
    let array =
      match lookup_cache ad map.c with
      | Some t -> t
      | None ->
          let line = ZMap.find ad map.map in
          map.c <- add_to_cache ad line map.c;
          line
    in
    Array.set array (array_bits x) (Some va);
    map.imp_count <- map.imp_count + 1;
    {
      c = map.c;
      map = map.map;
      fn_count = map.fn_count + 1;
      imp_count = map.imp_count;
    }
  with Not_found ->
    insert x va
      {
        c = [];
        map = ZMap.add (Z.shift_right x 12) (Array.make 512 None) map.map;
        fn_count = map.fn_count + 1;
        imp_count = fst (map.imp_count, (map.imp_count <- map.imp_count + 1));
      }

let lookup x map =
  assert (map.fn_count = map.imp_count);
  let ma = map_bits x in
  match lookup_cache ma map.c with
  | Some t -> t.(array_bits x)
  | None -> (
      try
        let ad = map_bits x in
        let line = ZMap.find ad map.map in
        map.c <- add_to_cache ad line map.c;
        line.(array_bits x)
      with Not_found -> None)
