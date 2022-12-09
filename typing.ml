open Format
open Lib
open Ast
open Tast

let debug = ref false
let dummy_loc = (Lexing.dummy_pos, Lexing.dummy_pos)

exception Error of Ast.location * string
exception Anomaly of string

let error loc e = raise (Error (loc, e))

(* TODONE environnement pour les types structure *)
let structure_env = Hashtbl.create 1

(* TODONE pour les fonctions *)
let fonction_env = Hashtbl.create 1

let rec type_type = function
  | PTident { id = "int" } -> Tint
  | PTident { id = "bool" } -> Tbool
  | PTident { id = "string" } -> Tstring
  | PTptr ty -> Tptr (type_type ty)
  | PTident { id; loc } -> (
      try Tstruct (Hashtbl.find structure_env id) with
      | Not_found -> error loc "unknown struct "
      | _ -> error dummy_loc "unknown struct ")
(* TODO type structure *)

let rec eq_type ty1 ty2 =
  match (ty1, ty2) with
  | Tint, Tint | Tbool, Tbool | Tstring, Tstring -> true
  | Tstruct s1, Tstruct s2 -> s1 == s2
  | t1, Tmany [ t2 ] | Tmany [ t1 ], t2 -> eq_type t1 t2
  | Tptr Twild, Tptr _ | Tptr _, Tptr Twild -> true
  | Tptr ty1, Tptr ty2 -> eq_type ty1 ty2
  | _ -> false
(* TODONE autres types *)

let unfold_typList = function
  | [ Tmany l ] | l ->
      List.map
        (function
          | Tmany (_ :: _ :: _) ->
              error dummy_loc "Trop d'arguments dans ta fonction"
          | Tmany [ t ] | t -> t)
        l

let fmt_used = ref false
let fmt_imported = ref false
let evar v = { expr_desc = TEident v; expr_typ = v.v_typ }

let new_var =
  let id = ref 0 in
  fun x loc ?(used = false) ty ->
    incr id;
    {
      v_name = x;
      v_id = !id;
      v_loc = loc;
      v_typ = ty;
      v_used = used;
      v_addr = 0;
      v_depth = 0;
    }

module Env = struct
  module M = Map.Make (String)

  type t = var M.t

  let empty = M.empty
  let find = M.find
  let add env v = M.add v.v_name v env
  let all_vars = ref []

  let check_unused () =
    let check v =
      if v.v_name <> "_" && (* TODO used *) true then
        error v.v_loc "unused variable"
    in
    List.iter check !all_vars

  let var x loc ?used ty env =
    let v = new_var x loc ?used ty in
    all_vars := v :: !all_vars;
    (add env v, v)

  (* TODO type () et vecteur de types *)
end

let tvoid = Tmany []
let make d ty = { expr_desc = d; expr_typ = ty }
let stmt d = make d tvoid

let rec a_t_on_une_l_value e =
  match e.pexpr_desc with
  | PEident _ -> true
  | PEdot (e, x) -> a_t_on_une_l_value e
  | PEunop (Ustar, e) -> e.pexpr_desc <> PEnil
  | _ -> false

let rec expr env e =
  let e, ty, rt = expr_desc env e.pexpr_loc e.pexpr_desc in
  ({ expr_desc = e; expr_typ = ty }, rt)

and expr_desc env loc = function
  | PEskip -> (TEskip, tvoid, false)
  | PEconstant c -> (
      (* TODONE *)
      match c with
      | Cbool x -> (TEconstant c, Tbool, false)
      | Cint x -> (TEconstant c, Tint, false)
      | Cstring x -> (TEconstant c, Tstring, false))
  | PEbinop (op, e1, e2) -> (
      (* TODONE *)
      let toto1 = fst (expr env e1) in
      let toto2 = fst (expr env e2) in
      match op with
      | Beq | Bne ->
          if toto1.expr_desc = TEnil && toto2.expr_desc = TEnil then
            error loc "e1 ou e2 était nill"
          else (TEbinop (op, toto1, toto2), Tbool, false)
      | Badd | Bsub | Bmul | Bdiv | Bmod ->
          let a1, b1 = expr env e1 in
          let a2, b2 = expr env e2 in
          if a1.expr_typ = Tint && a1.expr_typ = Tint then
            (TEbinop (op, a1, a2), Tint, false)
          else error loc "tu opérates sur des non int"
      | Band | Bor ->
          let a1, b1 = expr env e1 in
          let a2, b2 = expr env e2 in
          if a1.expr_typ = Tbool && a1.expr_typ = Tbool then
            (TEbinop (op, a1, a2), Tbool, false)
          else error loc "tu logicionnes sur des non bool"
      | Blt | Ble | Bgt | Bge ->
          let a1, b1 = expr env e1 in
          let a2, b2 = expr env e2 in
          if a1.expr_typ = Tint && a1.expr_typ = Tint then
            (TEbinop (op, a1, a2), Tbool, false)
          else error loc "tu compares des non int")
  | PEunop (Uamp, e1) ->
      (* TODONE *)
      if a_t_on_une_l_value e1 then
        (TEunop (Uamp, fst (expr env e1)), (fst (expr env e1)).expr_typ, false)
      else error loc "tu ampionnes un non l_value"
  | PEunop (Uneg, e1) ->
      (* TODONE *)
      let a1, b1 = expr env e1 in
      if a1.expr_typ = Tint then (TEunop (Uneg, a1), Tint, false)
      else error loc "tu négationnes un non int"
  | PEunop (Unot, e1) ->
      (* TODONE *)
      let a1, b1 = expr env e1 in
      if a1.expr_typ = Tbool then (TEunop (Uneg, a1), Tbool, false)
      else error loc "tu notionnes un non bool"
  | PEunop (Ustar, e1) ->
      (* TODONE *)
      let a1, b1 = expr env e1 in
      if not (a1.expr_desc = TEnil) then (TEunop (Ustar, a1), a1.expr_typ, false)
      else error loc "tu staronnes un nill"
  | PEcall ({ id = "fmt.Print" }, el) ->
      (* TODONE *)
      fmt_used := true;
      let rec aux l =
        match l with
        | [] -> ([], [])
        | p :: q ->
            let a1, b1 = expr env p in
            let toto, titi = aux q in
            (a1 :: toto, a1.expr_typ :: titi)
      in
      let toto, titi = aux el in
      let titi = unfold_typList titi in
      (TEprint toto, tvoid, false)
  | PEcall ({ id = "new" }, [ { pexpr_desc = PEident { id;loc } } ]) ->
      let ty = type_type (PTident { id;loc })
      in
      (TEnew ty, Tptr ty, false)
  | PEcall ({ id = "new" }, _) -> error loc "new expects a type"
  | PEcall (id, el) -> (* TODO *) assert false
  | PEfor (e, b) ->
      (* TODONE *)
      let a1, b1 = expr env e in
      let a2, b2 = expr env b in
      if a1.expr_typ = Tbool then (TEfor (a1, a2), tvoid, false)
      else error loc "tu foronnes un non bool"
  | PEif (e1, e2, e3) ->
      (* TODONE *)
      let a1, b1 = expr env e1 in
      let a2, b2 = expr env e2 in
      let a3, b3 = expr env e3 in
      if a1.expr_typ = Tbool then (TEif (a1, a2, a3), tvoid, b2 && b3)
      else error loc "tu ifonnes un non bool"
  | PEnil ->
      (* TODONE *)
      (TEnil, Tptr Twild, false)
  | PEident { id; loc } -> (
      (* TODONE *)
      try
        let v = Env.find id env in
        v.v_used <- true;
        (TEident v, v.v_typ, false)
      with Not_found -> error loc "Ta variable est introuvable !")
  | PEdot (e, id) -> (* TODO *) assert false
  | PEassign (lvl, el) -> (* TODO *) (TEassign ([], []), tvoid, false)
  | PEreturn el -> (* TODO *) (TEreturn [], tvoid, true)
  | PEblock el -> (* TODO *) (TEblock [], tvoid, false)
  | PEincdec (e, op) -> (* TODO *) assert false
  | PEvars _ -> error loc "Unexpected déclaration de var !"

let found_main = ref false

(* 1. declare structures *)

let phase1 = function
  | PDstruct { (*TODONE *) ps_name = { id; loc } } ->
      let dskldhjlsdqfjs = { id; loc } in
      if Hashtbl.mem structure_env dskldhjlsdqfjs.id then
        error loc "Déjà utilisé ton id, petit golem"
      else
        let titi =
          {
            s_name = dskldhjlsdqfjs.id;
            s_fields = Hashtbl.create 3;
            s_size = 0;
          }
        in
        Hashtbl.add structure_env dskldhjlsdqfjs.id titi
  | PDfunction _ -> ()

let rec sizeof = function
  (* TODONE *)
  | Tint | Tbool | Tstring | Tptr _ -> 8
  | Tmany l -> List.fold_left (fun a b -> a + sizeof b) 0 l
  | Tstruct x -> x.s_size
  | Twild -> 0

(* 2. declare functions and type fields *)
let rec type_bien_forme = function
  | PTident { id; loc } ->
      id = "bool" || id = "int" || id = "string" || Hashtbl.mem structure_env id
  | PTptr t -> type_bien_forme t

let phase2 = function
  | PDfunction { pf_name = { id; loc }; pf_params = pl; pf_typ = tyl } ->
      (* TODONE *)
      let kljkksfdf = { id; loc } in

      if id = "main" && pl = [] && tyl = [] then found_main := true
      else if id = "main" then error loc "Ton main est mal défini, petit golem";

      if Hashtbl.mem fonction_env kljkksfdf.id then
        error loc "Déjà utilisé ton id de ta fonction, petit golem"
      else
        let new_pl = ref [] in
        let rec pl_to_new_pl l =
          match l with
          | [] -> ()
          | p :: q ->
              let x = new_var (fst p).id (fst p).loc (type_type (snd p)) in
              new_pl := x :: !new_pl;
              pl_to_new_pl q
        in
        pl_to_new_pl pl;

        let new_tyl = ref [] in
        let rec tyl_to_new_tyl l =
          match l with
          | [] -> ()
          | p :: q ->
              let x = type_type p in
              new_tyl := x :: !new_tyl;
              tyl_to_new_tyl q
        in
        tyl_to_new_tyl tyl;

        let titi =
          { fn_name = kljkksfdf.id; fn_params = !new_pl; fn_typ = !new_tyl }
        in
        Hashtbl.add fonction_env kljkksfdf.id titi;
        let nom_variables_de_la_fonction = Hashtbl.create (List.length pl) in

        let rec aux1 l =
          match l with
          | [] -> ()
          | p :: q ->
              if not (type_bien_forme p) then
                error loc "Ton type de var est mal formé, petit golem"
              else aux1 q
        in
        aux1 tyl;

        let rec aux2 l =
          match l with
          | [] -> ()
          | p :: q ->
              if Hashtbl.mem nom_variables_de_la_fonction (fst p).id then
                error (fst p).loc "Déjà utilisé ton id de ta var, petit golem"
              else (
                Hashtbl.add nom_variables_de_la_fonction (fst p).id ();
                if not (type_bien_forme (snd p)) then
                  error (fst p).loc "Ton type de var est mal formé, petit golem"
                else aux2 q)
        in
        aux2 pl
  | PDstruct { ps_name = { id; loc }; ps_fields = fl } -> (
      (* TODONE *)
      let pqfjmqhf = { id; loc } in
      try
        let toto = Hashtbl.find structure_env pqfjmqhf.id in
        let rec aux l titi =
          match l with
          | [] -> titi
          | p :: q ->
              if Hashtbl.mem toto.s_fields (fst p).id then
                error (fst p).loc
                  "Déjà utilisé ton id de ton champ, petit golem"
              else (
                Hashtbl.add toto.s_fields (fst p).id
                  {
                    f_name = (fst p).id;
                    f_typ = type_type (snd p);
                    f_ofs = titi / 8;
                  };
                if not (type_bien_forme (snd p)) then
                  error (fst p).loc
                    "Ton type de ton champ est mal formé, petit golem"
                else aux q (titi + sizeof (type_type (snd p))))
        in
        toto.s_size <- aux fl 0
      with Not_found -> error pqfjmqhf.loc "Ta strucure est introuvable !")

(* 3. type check function bodies *)
let decl = function
  | PDfunction
      { pf_name = { id; loc }; pf_body = e; pf_typ = tyl; pf_params = pl } ->
      (* TODO check name and type *)
      let toto = ref Env.empty in
      let new_pl = ref [] in
      let rec pl_to_new_pl l =
        match l with
        | [] -> ()
        | p :: q ->
            let x = new_var (fst p).id (fst p).loc (type_type (snd p)) in
            new_pl := x :: !new_pl;
            pl_to_new_pl q
      in
      pl_to_new_pl pl;

      let new_tyl = ref [] in
      let rec tyl_to_new_tyl l =
        match l with
        | [] -> ()
        | p :: q ->
            let x = type_type p in
            new_tyl := x :: !new_tyl;
            tyl_to_new_tyl q
      in
      tyl_to_new_tyl tyl;

      let f = { fn_name = id; fn_params = !new_pl; fn_typ = !new_tyl } in
      let e, rt = expr !toto e in
      TDfunction (f, e)
  | PDstruct { ps_name = { id; loc } } -> (
      (* TODONE *)
      let msqkfhmqo = { id; loc } in
      let s = { s_name = id; s_fields = Hashtbl.create 5; s_size = 0 } in
      try
        let toto = Hashtbl.find structure_env msqkfhmqo.id in
        let rec aux x =
          Hashtbl.iter
            (fun _ field ->
              match field.f_typ with
              | Tstruct a ->
                  if a.s_name = id then
                    error dummy_loc "Ta strucure est récursive !"
                  else aux a.s_fields
              | _ -> ())
            x
        in
        aux toto.s_fields;
        TDstruct s
      with Not_found -> error msqkfhmqo.loc "Ta strucure est introuvable !")

let file ~debug:b (imp, dl) =
  debug := b;
  (* fmt_imported := imp; *)
  List.iter phase1 dl;
  List.iter phase2 dl;
  if not !found_main then error dummy_loc "missing method main";
  let dl = List.map decl dl in
  Env.check_unused ();
  (* TODO variables non utilisees *)
  if imp && not !fmt_used then error dummy_loc "fmt imported but not used";
  dl
