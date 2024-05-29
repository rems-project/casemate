type 'a cache
type 'a t

val empty : 'a t
val insert : Z.t -> 'a -> 'a t -> 'a t
val lookup : Z.t -> 'a t -> 'a option
