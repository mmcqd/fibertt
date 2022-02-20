
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
  | Sig of signature
  | Struct of (string * t) list
  | Proj of string * t
  
and tp = t

and signature =
  | Nil
  | Cons of string * tp * signature

and quantifier = string * tp * tp
[@@ deriving show {with_path = false}]


