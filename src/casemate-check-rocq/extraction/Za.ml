include Z

let mask64 = (~$1 lsl 64) - ~$1
let of_nat a = a
let to_nat a = a

let[@inline] add64 a b =
  let x = a + b in
  if Z.leq x mask64 then x else x land mask64

let[@inline] mul64 a b =
  let x = a * b in
  if Z.leq x mask64 then x else x land mask64

let and64 a b = a land b
let shr64 a b = shift_right a (to_int b)
let shl64 a b = shift_left a (to_int b) land mask64
