type +'a t = ('a -> unit) -> unit

let nil _ = ()
let (@:) x t i = i x; t i

let of_f t = t
let iter f t = t f

let ret x i = i x
let map f t i = t (fun x -> i (f x))
let ( let* ) t f i = t (fun x -> f x i)
let ( let+ ) t f i = map f t i

let filter_map f t i = t (fun x -> match f x with Some y -> i y | _ -> ())
let fold f z t =
  let acc = ref z in
  t (fun x -> acc := f !acc x);
  !acc

(* IO *)

let rec lines ic i = match input_line ic with
| exception End_of_file -> ()
| line -> i line; lines ic i

let in_file path f i =
  let ic = open_in path in
  Fun.protect ~finally:(fun () -> close_in ic) (fun () -> f ic i)
