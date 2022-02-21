open Core

type _t =
  | U
  | Var of string
  | Lam of string list * t
  | Pi of tele * t
  | Ap of t * t list
  | Singleton of {tm : t ; tp : t}
  | Sig of (string * t) list
  | Struct of (string * t) list
  | Proj of string * t
  | Patch of t * [`Patch of string * t | `Var of string] list
  | Point of t
  | Hole
  | Total of t
  [@@deriving show {with_path = false}]

and t = {con : _t ; loc : loc}
  [@@deriving show {with_path = false}]

and loc = Lexing.position * Lexing.position
  [@opaque]

and tele = (string list * t) list

let show_pos (pos : Lexing.position) = sprintf "%i:%i" pos.pos_lnum (pos.pos_cnum - pos.pos_bol + 1)
let show_loc ((s,e) : loc) = 
  let fname = match s.pos_fname with "" -> "repl" | f -> f in
  sprintf "%s - %s-%s" fname (show_pos s) (show_pos e)


let rec seek_line c = function
  | 1 -> ()
  | n -> ignore @@ Stdlib.input_line c; seek_line c (n-1)

let show_loc_code ((s,e) : loc) = if String.equal s.pos_fname "" then show_loc (s,e) else
  let c = Stdlib.open_in s.pos_fname in
  let start_ = s.pos_cnum - s.pos_bol in
  let end_ = e.pos_cnum - e.pos_bol in
  seek_line c s.pos_lnum;
  let code = Stdlib.input_line c in
  Stdlib.close_in c;
  let line_str = sprintf "%d | " s.pos_lnum in
  let offset = start_ + String.length line_str in
  let highlight = end_ - start_ - 2 in
  sprintf "%s\n%s%s\n" (show_loc (s,e)) line_str code ^
  if highlight >= 0 
  then sprintf "%s^%s^" (String.init offset ~f:(fun _ -> ' ')) (String.init highlight ~f:(fun _ -> '_'))
  else sprintf "%s^" (String.init offset ~f:(fun _ -> ' '))

type cmd =
  | Eval of t
  | Def of {name : string ; tm : t}
  | DefChk of {name : string ; tm : t ; tp : t}
  | DefFun of {name : string ; doms : (string list * t) list ; ran : t ; body : t}
  | Import of string
