module ZMap = Map.Make (Z)

type 'a cache = (Z.t * 'a option array) list

type 'a t = {
  mutable c : 'a cache;
  map : 'a option array ZMap.t;
  (* Those two counters ensures that this imperative implementation
     behaves like a functional implementation by updating a counter
     on the callee object, so that if it is reused, only the imperative
     counter will be incremented leading to an assertion fail. *)
  mutable is_valid : bool;
}

let cache_size = 2
let empty () = { c = []; map = ZMap.empty; is_valid = true }
let map_bits x = Z.shift_right x 9
let array_bits x = Z.(to_int (logand x (of_int 0x1ff)))

let rec lookup_cache addr : 'a cache -> 'b = function
  | [] -> None
  | (a, t) :: _ when Z.equal a addr -> Some t
  | _ :: q -> lookup_cache addr q

let rec is_cached x i : 'a cache -> 'a cache = function
  | [] -> []
  | _ when i = 0 -> []
  | (a, _) :: q when Z.equal a x -> q
  | t :: q -> t :: is_cached x (i - 1) q

let add_to_cache addr line (cache : 'a cache) =
  (addr, line) :: is_cached addr cache_size cache

let rec insert x va map =
  assert map.is_valid;
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
    map.is_valid <- false;
    { c = map.c; map = map.map; is_valid = true }
  with Not_found ->
    insert x va
      {
        c = [];
        map = ZMap.add (map_bits x) (Array.make 512 None) map.map;
        is_valid = true;
      }

let lookup x map =
  assert map.is_valid;
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

let array_fold_left f ar init =
  let res = ref init in
  for i = 0 to Array.length ar - 1 do
    res := f i ar.(i) !res
  done;
  !res

let fold f m init =
  let g addr =
    array_fold_left (fun k v ini ->
        match v with
        | Some v -> f (Z.add (Z.shift_left addr 9) (Z.of_int k)) v ini
        | None -> ini)
  in
  ZMap.fold g m.map init
