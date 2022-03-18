open! Core

type t =
  | U
  | Lam of string * Syn.t clo
  | Pi of string * t * Syn.t clo
  | InS of t
  | Singleton of {tm : t ; tp : tp}
  | Struct of structure
  | Sig of signature
  | Neu of {hd : head ; sp : spine ; tp : t}

and head =
  | Lvl of int
  | Def of {name : string ; value : t Lazy.t [@opaque] }

and elim =
  | Ap of {tm : t ; tp : t [@opaque]}
  | Proj of string
  (* | Patch of signature *)

and spine = elim list

and structure = (string * t) list

and signature = 
  | Nil
  | Cons of string * tp * Syn.signature clo

and tp = t

and 'a clo = {tm : 'a ; env : env [@opaque]}

and env = t list
[@@deriving show {with_path = false}]

let var tp lvl = Neu {hd = Lvl lvl ; sp = [] ; tp}