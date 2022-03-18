open! Core


module type S =
sig
  type 'a t 
  val ret : 'a -> 'a t

  val (>>=) : 'a t -> ('a -> 'b t) -> 'b t
  val (let*) : 'a t -> ('a -> 'b t) -> 'b t

  val (<$>) : ('a -> 'b) -> 'a t -> 'b t
  val (let+) : 'a t -> ('a -> 'b) -> 'b t
  val (and+) : 'a t -> 'b t -> ('a * 'b) t

  val sequence : 'a t list -> 'a list t 
end

module type Reader =
sig
  include S
  type local
  val read : local t
  val scope : (local -> local) -> 'a t -> 'a t
  val run : 'a t -> local -> ('a,exn) result
  val run_exn : 'a t -> local -> 'a

  val fail : exn -> 'a t

  val catch : 'a t ->  ('a,exn) result t
end

module Reader (X : sig type local end) : Reader with type 'a t = X.local -> ('a,exn) result and type local = X.local =
struct
  type local = X.local
  type 'a t = local -> ('a,exn) result
  
  let ret x = fun _ -> Ok x 

  let (let*) r f = fun l ->
    match r l with
      | Ok e -> f e l
      | Error e -> Error e

  let (>>=) = (let*)

  let (let+) r f = fun l -> 
    match r l with
      | Ok e -> Ok (f e)
      | Error e -> Error e

  let (<$>) f x = (let+) x f

  let (and+) r1 r2 =
    let* a = r1 in
    let* b = r2 in
    ret (a,b)
  let read = fun l -> Ok l
  let scope f r = fun l -> r (f l)

  let rec sequence = function
    | [] -> ret []
    | x :: xs ->
      let* x = x in
      let+ xs = sequence xs in
      x :: xs
  let run = Fun.id

  let run_exn r l =
    match r l with
      | Ok e -> e
      | Error e -> raise e
    
  let fail e = fun _ -> Error e

  let catch r = fun l -> Ok (r l)
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

  val run : global -> local -> 'a t -> ('a,exn) result

  val run_exn : global -> local -> 'a t -> 'a 

  val fail : exn -> 'a t

  val catch : 'a t -> ('a,exn) result t
end

module ReaderState (X : sig type global type local end) : ReaderState with type global = X.global and type local = X.local and type 'a t = X.global * X.local -> X.global * ('a,exn) result =
struct
  type global = X.global
  type local = X.local

  type 'a t = global * local -> global * ('a,exn) result

  let ret x = fun (g,_) -> (g,Ok x)

  let ( let* ) rs f = fun (g,l) ->
    let (g',x) = rs (g,l) in
    match x with
      | Ok x -> f x (g',l)
      | Error e -> (g', Error e)

  let (>>=) = (let*)
  
  let (let+) (rs : 'a t) (f : 'a -> 'b) : 'b t =
    let* x = rs in
    ret (f x)

  let (<$>) f x = (let+) x f

  let (and+) r1 r2 =
    let* a = r1 in
    let* b = r2 in
    ret (a,b)

  let read = fun (g,l) -> (g,Ok l)
  let local f rs = fun (g,l) -> rs (g, f l)

  let get = fun (g,_) -> (g,Ok g)
  let set g' = fun _ -> (g',Ok ())
  let modify f = fun (g,_) -> (f g, Ok ())

  let rec sequence = function
    | [] -> ret []
    | x :: xs ->
      let* x = x in
      let+ xs = sequence xs in
      x :: xs
  let run g l rs = snd @@ rs (g,l)

  let run_exn g l rs = 
    match snd @@ rs (g,l) with
      | Ok e -> e
      | Error e -> raise e
    
  let fail e = fun (g,_) -> (g,Error e)

  let catch rs = fun st ->
    let (g,e) = rs st in 
    (g, Ok e)
end

