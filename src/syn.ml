
type t = 
  | U
  | Idx of int
  | Def of string
  | Pi of quantifier
  | Lam of string * t
  | Ap of t * t
  | Singleton of {tm : t ; tp : tp}
  | InS of t
  | OutS of t
  | RTyCons of quantifier
  | RTyNil
  | RCons of string * t * t
  | RNil
  | Proj of string * t
  | Rest of t
  

and tp = t


and quantifier = string * tp * tp
[@@ deriving show {with_path = false}]


