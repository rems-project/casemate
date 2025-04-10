type 'a cache
type 'a t

val empty : unit -> 'a t
val insert : Z.t -> 'a -> 'a t -> 'a t
val lookup : Z.t -> 'a t -> 'a option
val fold : (Z.t -> 'a -> 'b -> 'b) -> 'a t -> 'b -> 'b
