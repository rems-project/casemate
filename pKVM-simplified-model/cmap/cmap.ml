module ZMap = Map.Make (Z)

type 'a cache = (Z.t * 'a option array) list
type 'a t = { c : 'a cache; map : 'a option array ZMap.t }

let empty = { c = []; map = ZMap.empty }
let map_bits x = Z.shift_right x 12
let array_bits x = Z.(to_int (shift_right (logand x (of_int 0xfff)) 3))

let rec insert x va ma =
  try
    let array = ZMap.find (map_bits x) ma.map in
    Array.set array (array_bits x) (Some va);
    ma
  with Not_found ->
    insert x va
      {
        c = [];
        map = ZMap.add (Z.shift_right x 12) (Array.make 512 None) ma.map;
      }

let lookup x ma =
  try (ZMap.find (map_bits x) ma.map).(array_bits x) with Not_found -> None

let () = ignore empty.c
