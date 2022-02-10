open! Core

type t =
  | U
  | Lam of string * clo
  | Pi of string * t * clo
  | InS of t
  | Singleton of {tm : t ; tp : tp}
  | Neu of {hd : head ; sp : spine ; tp : t [@opaque]}

and head =
  | Lvl of int
  | Def of {name : string ; value : t Lazy.t [@opaque] }

and elim =
  | Ap of {tm : t ; tp : t [@opaque]}
  | OutS of {tm : t ; tp : t}

and spine = elim list

and tp = t

and clo = {syn : Syn.t ; env : env [@opaque]}

and env = t list
[@@deriving show {with_path = false}]

let var tp lvl = Neu {hd = Lvl lvl ; sp = [] ; tp}