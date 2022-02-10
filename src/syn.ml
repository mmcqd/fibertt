
type t = 
  | U
  | Idx of int
  | Def of string
  | Lam of string * t
  | Ap of t * t
  | Pi of quantifier
  | Singleton of {tm : t ; tp : tp}
  | InS of t
  | OutS of t

and tp = t


and quantifier = string * tp * tp
[@@ deriving show {with_path = false}]


