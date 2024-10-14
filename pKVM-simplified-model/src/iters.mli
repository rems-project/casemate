type +'a t

val nil : 'a t
val (@:) : 'a -> 'a t -> 'a t

val of_f : (('a -> unit) -> unit) -> 'a t
val iter : ('a -> unit) -> 'a t -> unit

val ret : 'a -> 'a t
val map : ('a -> 'b) -> 'a t -> 'b t
val ( let* ) : 'a t -> ('a -> 'b t) -> 'b t
val ( let+ ) : 'a t -> ('a -> 'b) -> 'b t

val filter_map : ('a -> 'b option) -> 'a t -> 'b t
val fold : ('a -> 'b -> 'a) -> 'a -> 'b t -> 'a
val fold_result : ('a -> 'b -> ('a, 'c) result) -> 'a -> 'b t -> ('a, 'c) result

val take : int -> 'a t -> 'a t

val in_file : string -> (in_channel -> 'a t) -> 'a t
val lines : in_channel -> string t
