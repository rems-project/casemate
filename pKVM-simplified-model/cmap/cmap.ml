module ZMap = Map.Make (Z)

type 'a cache = (Z.t * 'a option array) list
type 'a t = { c : 'a cache; map : 'a ZMap.t }

let empty = { c = []; map = ZMap.empty }
let insert x va ma = { c = []; map = ZMap.add x va ma.map }
let lookup k ma = try Some (ZMap.find k ma.map) with Not_found -> None
let () = ignore empty.c
