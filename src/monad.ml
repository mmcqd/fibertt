open! Core


module type S =
sig
  type 'a t 
  val ret : 'a -> 'a t
  val (let*) : 'a t -> ('a -> 'b t) -> 'b t

  val (<$>) : ('a -> 'b) -> 'a t -> 'b t
  val (let+) : 'a t -> ('a -> 'b) -> 'b t
  val (and+) : 'a t -> 'b t -> ('a * 'b) t
end

module type Reader =
sig
  include S
  type local
  val read : local t
  val scope : (local -> local) -> 'a t -> 'a t
  val run : 'a t -> local -> 'a
end

module Reader (X : sig type local end) : Reader with type 'a t = X.local -> 'a and type local = X.local =
struct
  type local = X.local
  type 'a t = local -> 'a
  
  let ret x = fun _ -> x 
  let (let*) r f = fun l -> f (r l) l
  let (let+) r f = fun l -> f (r l)
  let (<$>) f x = (let+) x f

  let (and+) r1 r2 =
    let* a = r1 in
    let* b = r2 in
    ret (a,b)
  let read = fun l -> l
  let scope f r = fun l -> r (f l)

  let run = Fun.id
end

module type ReaderState =
sig
  include S
  type local
  type global

  val read : local t
  val local : (local -> local) -> 'a t -> 'a t

  val get : global t
  val set : global -> unit t
  val modify : (global -> global) -> unit t

  val run : global -> local -> 'a t -> 'a
end

module ReaderState (X : sig type global type local end) : ReaderState with type global = X.global and type local = X.local =
struct
  type global = X.global
  type local = X.local

  type 'a t = global * local -> global * 'a

  let ret x = fun (g,_) -> (g,x)

  let ( let* ) rs f = fun (g,l) ->
    let (g',x) = rs (g,l) in
    f x (g',l)
  let (let+) (rs : 'a t) (f : 'a -> 'b) : 'b t =
    let* x = rs in
    ret (f x)

  let (<$>) f x = (let+) x f

  let (and+) r1 r2 =
    let* a = r1 in
    let* b = r2 in
    ret (a,b)

  let read = fun (g,l) -> (g,l)
  let local f rs = fun (g,l) -> rs (g, f l)

  let get = fun (g,_) -> (g,g)
  let set g' = fun _ -> (g',())
  let modify f = fun (g,_) -> (f g, ())

  let run g l rs = snd @@ rs (g,l)
end

