module M = Monad
open Core


module Local_ctx =
struct
  type t = {env : Dom.env ; tps : (string * (int * Dom.t)) list; lvl : int}
  [@@deriving show]

  let lvl_to_idx lvl l = lvl - (l + 1)
  let empty = {env = [] ; tps = [] ; lvl = 0}
  let extend ~name ~tp ~ctx:{env ; tps ; lvl} = {env = Dom.var tp lvl :: env ; tps = (name,(lvl,tp)) :: tps ; lvl = lvl+1}
  let let_extend ~name ~tp ~tm ~ctx:{env ; tps ; lvl} = {env = tm :: env ; tps = (name, (lvl,tp)) :: tps ; lvl = lvl+1}

  let find_idx i ctx : Dom.t = List.nth_exn ctx.env i
   
  let find_tp_and_idx x ctx = let (let+) = Option.(>>|) in 
    let+ l,tp = List.Assoc.find ~equal:String.equal ctx.tps x in
    lvl_to_idx ctx.lvl l, tp


end

module Global_ctx =
struct
  (* tp,tm *)
  type t = {ctx : (string * (Dom.t * Dom.t)) list}
  [@@deriving show]

  let empty = {ctx = []}
  let extend ~name ~tm ~tp ~ctx = {ctx = (name, (tp,tm)) :: ctx.ctx}


  let find_name ~name ~ctx = List.Assoc.find ~equal:String.equal ctx.ctx name

  let find_name_exn ~name ~ctx = List.Assoc.find_exn ~equal:String.equal ctx.ctx name
end

module PrintLocal =
struct 
  type local = string list 
end

module CompLocal =
struct
  type local = Global_ctx.t
end

module ElabLocal =
struct
  type local = {local : Local_ctx.t ; global : Global_ctx.t ; loc : Raw.loc}
end

module EvalLocal =
struct
  type local = {env : Dom.env ; global : Global_ctx.t}
end

module QuoteLocal =
struct
  type local = {unfold : bool ; lvl : int ; global : Global_ctx.t}
end

module ConvLocal =
struct
  type local = {lvl : int ; global : Global_ctx.t ; names : string list}
end

module CmdState =
struct
  type local = { importing : string list }
  type global = { global : Global_ctx.t ; imported : string list }
end


module PrintMonad =
struct
  include M.Reader (PrintLocal)
  type 'a print = 'a t

  let abstract name =
    scope (fun names -> name :: names)

  let idx (i : int) : string print =
    let+ names = read in
    List.nth_exn names i
    
end
type 'a print = 'a PrintMonad.t


module CompMonad =
struct
  include M.Reader (CompLocal)
  type 'a comp = 'a t

  let read_ctx =
    let+ global = read in 
    global.ctx
  
  let lift_eval = fun env ev global ->
    ev EvalLocal.{global ; env}
end
type 'a comp = 'a CompMonad.t

module ElabMonad =
struct
  include M.Reader (ElabLocal)

  exception Hole of string
  exception Error of string

  type 'a elab = 'a t
  let read_local : Local_ctx.t elab =
    let+ ctx = read in
    ctx.local
  let read_global : Global_ctx.t elab =
    let+ ctx = read in
    ctx.global

  let find_idx idx : Dom.t elab =
    let+ ctx = read_local in
    Local_ctx.find_idx idx ctx

  let lift_print : 'a print -> 'a elab = fun p ctx ->
    p (List.map ~f:fst ctx.local.tps)

  let lift_comp : 'a comp -> 'a elab = fun c ctx -> 
    c ctx.global

  let lift_eval : (EvalLocal.local -> ('a,exn) result) -> 'a elab = fun ev {global ; local ; _} -> 
    ev {env = local.env ; global}

  let lift_quote : unfold:bool -> (QuoteLocal.local -> ('a,exn) result) -> 'a elab = fun ~unfold q {global ; local ; _} ->
    q {global ; lvl = local.lvl ; unfold}


  let lift_conv : (ConvLocal.local -> ('a,exn) result) -> 'a elab = fun cnv ctx ->
    cnv {lvl = ctx.local.lvl ; global = ctx.global ; names = List.map ~f:fst ctx.local.tps}

  let locally : (Local_ctx.t -> Local_ctx.t) -> 'a elab  -> 'a elab = fun f ->
    scope (fun ctx -> {ctx with local = f ctx.local})

  let globally : (Global_ctx.t -> Global_ctx.t) -> 'a elab -> 'a elab = fun f ->
    scope (fun ctx -> {ctx with global = f ctx.global})
    
  let abstract : name:string -> tp:Dom.tp -> (Dom.t -> 'a elab) -> 'a elab = fun ~name ~tp k ->
    locally (fun ctx -> Local_ctx.extend ~name ~tp ~ctx) @@
    let* v = find_idx 0 in
    k v

  let let_abstract : name:string -> tp:Dom.tp -> tm:Dom.t -> (Dom.t -> 'a elab) -> 'a elab = fun ~name ~tp ~tm k ->
    locally (fun ctx -> Local_ctx.let_extend ~name ~tp ~tm ~ctx) @@
    let* v = find_idx 0 in
    k v

  let define : name:string -> tm:Dom.t -> tp:Dom.tp -> 'a elab -> 'a elab = fun ~name ~tm ~tp ->
    globally (fun ctx -> Global_ctx.extend ~name ~tm ~tp ~ctx)

  
  let fail (e : exn) : 'a elab =
    let* ctx = read in
    let loc = ctx.loc in
    match e with
      | Error e -> fail @@ Error (Raw.show_loc_code loc ^ "\n\n" ^ e)
      | Hole e -> fail @@ Hole (Raw.show_loc_code loc ^ "\n" ^ e)
      | _ -> fail e

end
type 'a elab = 'a ElabMonad.t

module EvalMonad =
struct
  include M.Reader (EvalLocal)

  type 'a eval = 'a t

  let read_global : Global_ctx.t eval =
    let+ ctx = read in 
    ctx.global

  let read_env : Dom.env eval =
    let+ ctx = read in
    ctx.env

  let find_idx i : Dom.t eval =
    let+ env = read_env in
    List.nth_exn env i

  let find_name name : (Dom.tp * Dom.t) eval =
    let+ global = read_global in
    Global_ctx.find_name_exn ~name ~ctx:global


  let lift_comp : 'a comp -> 'a eval = fun cmp {global ; _} -> cmp global
    
  let locally : (Dom.env -> Dom.env) -> 'a eval -> 'a eval = fun f ->
    scope (fun ctx -> {ctx with env = f ctx.env})

  let extend : Dom.t -> 'a eval -> 'a eval = fun tm ->
    locally (fun ctx -> tm :: ctx)
 
  let multi_extend : Dom.t list -> 'a eval -> 'a eval = fun tms ->
    locally (fun ctx -> tms @ ctx)


end
type 'a eval = 'a EvalMonad.t

module QuoteMonad =
struct 
  include M.Reader (QuoteLocal)
  type 'a quote = 'a t

  let read_lvl : int quote =
    let+ ctx = read in
    ctx.lvl

  let read_unfold : bool quote =
    let+ ctx = read in
    ctx.unfold

  let read_global : Global_ctx.t quote =
    let+ ctx = read in
    ctx.global

  let lift_comp : 'a comp -> 'a quote = fun cmp ctx ->
    cmp ctx.global

  let abstract : tp:Dom.tp -> (Dom.t -> 'a quote) -> 'a quote = fun ~tp k ->
    let* lvl = read_lvl in
    scope (fun ctx -> {ctx with lvl = lvl + 1}) @@
    k (Dom.var tp lvl)
end
type 'a quote = 'a QuoteMonad.t

module ConvMonad =
struct
  include M.Reader (ConvLocal)

  exception Error of string
  type 'a conv = 'a t

  let read_lvl : int conv =
    let+ ctx = read in
    ctx.lvl

  let lift_quote : unfold:bool -> 'a quote -> 'a conv = fun ~unfold qu ctx ->
    qu {global = ctx.global ; unfold ; lvl = ctx.lvl}
  
  let lift_print : 'a print -> 'a conv = fun pr ctx ->
    pr ctx.names 

  let lift_comp : 'a comp -> 'a conv = fun cmp ctx ->
    cmp ctx.global

  let abstract : name:string -> tp:Dom.tp -> (Dom.t -> 'a conv) -> 'a conv = fun ~name ~tp k ->
    let* lvl = read_lvl in
    scope (fun ctx -> {ctx with lvl = lvl + 1 ; names = name :: ctx.names}) @@
    k (Dom.var tp lvl)
end
type 'a conv = 'a ConvMonad.t

module CmdMonad = 
struct
  include M.ReaderState (CmdState)
  type 'a cmd = 'a t

  let lift_print : 'a print -> 'a cmd = fun p (g,_) ->
    (g,PrintMonad.run p [])

  let lift_elab : Raw.loc -> 'a elab -> 'a cmd = fun loc e (g,_) ->
    (g,ElabMonad.run e {global = g.global ; local = Local_ctx.empty ; loc})

  let lift_quote : unfold:bool -> 'a quote -> 'a cmd = fun ~unfold q (g,_) ->
    (g,QuoteMonad.run q {global = g.global ; lvl = 0 ; unfold})
  let lift_eval : 'a eval -> 'a cmd = fun ev (g,_) ->
   (g,EvalMonad.run ev {global = g.global ; env = Local_ctx.empty.env})

  let define ~name ~tm ~tp : unit cmd =
    let* state = get in
    set {state with global = Global_ctx.extend ~name ~tm ~tp ~ctx:state.global}

  let import path : unit cmd =
    let* state = get in 
    set {state with imported = path :: state.imported}
end

type 'a cmd = 'a CmdMonad.t