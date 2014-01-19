(****************************************************************************)
(*  RelationExtraction - Extraction of inductive relations for Coq          *)
(*                                                                          *)
(*  This program is free software: you can redistribute it and/or modify    *)
(*  it under the terms of the GNU General Public License as published by    *)
(*  the Free Software Foundation, either version 3 of the License, or       *)
(*  (at your option) any later version.                                     *)
(*                                                                          *)
(*  This program is distributed in the hope that it will be useful,         *)
(*  but WITHOUT ANY WARRANTY; without even the implied warranty of          *)
(*  MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the           *)
(*  GNU General Public License for more details.                            *)
(*                                                                          *)
(*  You should have received a copy of the GNU General Public License       *)
(*  along with this program.  If not, see <http://www.gnu.org/licenses/>.   *)
(*                                                                          *)
(*  Copyright 2011, 2012 CNAM-ENSIIE                                        *)
(*                 Catherine Dubois <dubois@ensiie.fr>                      *)
(*                 David Delahaye <david.delahaye@cnam.fr>                  *)
(*                 Pierre-Nicolas Tollitte <tollitte@ensiie.fr>             *)
(****************************************************************************)

open Pred
open Coq_stuff
open Util
open Pp
open Miniml
open Nametab
open Libnames
open Names
open Term
open Extract_env
open Table

(* Gets an inductive global reference from the extract env. *)
let get_indgref env id =
  try List.assoc id env.extr_henv.ind_grefs with _ -> failwith "get_indgref"

(* Makes a dummy Coq global_reference. *)
let mk_dummy_glb (env, id_spec) id =
  let pred_glb = get_indgref env id_spec in
  let mod_path = modpath_of_r pred_glb in
  let dir_path = empty_dirpath in
  let lbl = mk_label (string_of_ident id) in
  ConstRef (make_con mod_path dir_path lbl)

(* Gets a constr from the extract env. *)
let get_cstr (env, id_spec) id =
  try List.assoc id env.extr_henv.cstrs with _ -> 
  let fake_gref = mk_dummy_glb (env, id_spec) id in
  constr_of_global fake_gref


(* References on Coq types. *)
let bool_glb () = locate (qualid_of_string "Coq.Init.Datatypes.bool")
let get_booleq () = MLglob (locate (qualid_of_string "Coq.Bool.Bool.eqb"))
let get_false () = MLcons (Tglob (bool_glb (), []), 
                     locate (qualid_of_string "Coq.Init.Datatypes.false"), [])
let get_true () = MLcons (Tglob (bool_glb (), []), 
                     locate (qualid_of_string "Coq.Init.Datatypes.true"), [])
let get_pfalse () =
  Pcons (locate (qualid_of_string "Coq.Init.Datatypes.false"), [])
let get_ptrue () =
  Pcons (locate (qualid_of_string "Coq.Init.Datatypes.true"), [])

(* Gets an MiniML id from a ident. *)
let ml_id_of_ident id = Id (id_of_string (string_of_ident id))

(* Finds the rel of an id in a list of binders, if it exists. *)
let find_rel bind id = 
  let rec rec_find_rel bind i = match bind with
  | [] -> None
  | id'::_ when id' = id -> Some i
  | _::bindt -> rec_find_rel bindt (i+1) in
  rec_find_rel bind 1

(* Finds the rel of an id in a list of binders, or fails. *)
let get_rel id bind = match find_rel bind id with
  | None -> anomalylabstrm "RelationExtraction" (str "Cannot find rel")
  | Some i -> i

(* Make a new rel for an id. *)
let rel_from_id id bind nbind = (List.length nbind) + 1, id::nbind

(* Generates a term in a pattern. *)
let rec gen_pat (env, id_spec) bind nbind (p,_) = match p with
  | MLPTuple pl -> let pats, nbind = List.fold_left 
      (fun (pats, nbind) p -> 
        let (pat, nbind) = gen_pat (env, id_spec) bind nbind p in
        (pats@[pat], nbind))
      ([], nbind) pl in
      ((Ptuple pats), nbind)
  | MLPConstr (id, pl) -> 
      let glb = global_of_constr (get_cstr (env, id_spec) id) in
      let pats, nbind = List.fold_left 
      (fun (pats, nbind) p -> 
        let (pat, nbind) = gen_pat (env, id_spec) bind nbind p in
        (pats@[pat], nbind))
      ([], nbind) pl in
      ((Pcons (glb, pats)), nbind)
  | MLPConst id -> (* we have to linearise *)
      (*let glb = global_of_constr (get_cstr (env, id_spec) id) in*)
      errorlabstrm "RelationExtraction" (str "TODO - constants in patterns")
  | MLPVar id -> let rel, nbind = rel_from_id id bind nbind in
      (Prel rel, nbind)
  | MLPWild -> (Pwild, nbind)
  | MLPATrue -> (get_ptrue (), nbind)
  | MLPAFalse -> (get_pfalse (), nbind)
  | _ -> anomalylabstrm "RelationExtraction" (str "Unknown pattern in MiniML")

(* Generates a term. *)
and gen_term (env, id_spec) default bind (t,_) = match t with
  | MLTVar id -> MLrel (get_rel id bind)
  | MLTTuple tl -> MLtuple (List.map (gen_term (env, id_spec) default bind) tl)
  | MLTConstr (id, tl) -> 
    let cstr = get_cstr (env, id_spec) id in
    let ref = global_of_constr cstr in
    MLcons (Tglob (ref, []), ref,
      List.map (gen_term (env, id_spec) default bind) tl)
  | MLTConst id -> let s = string_of_ident id in
    let ref = try let i = String.rindex s '#' in
        let n_name = String.sub s (i+1) (String.length s - i - 1) in
        mk_dummy_glb (env, id_spec) (ident_of_string n_name)
      with Not_found | Invalid_argument _ ->
        let cstr = get_cstr (env, id_spec) id in
        global_of_constr cstr 
    in 
    MLglob ref
  | MLTFun (i, tl, _) | MLTFunNot (i, tl, _) -> (* TODO: the *not* case *)
    let glb = 
      if string_of_ident i = "eq_full" then
        mk_dummy_glb (env, id_spec) (ident_of_string "(=)")
      else
        try global_of_constr (get_cstr (env, id_spec) i) 
        with Not_found -> mk_dummy_glb (env, id_spec) i in
    MLapp (MLglob glb, List.map (gen_term (env, id_spec) default bind) tl)
  | MLTATrue -> get_true ()
  | MLTAFalse -> get_false ()
  | MLTMatch (t, _, ptl) ->
  let t = gen_term (env, id_spec) default bind t in
  let pats = List.map (fun (p, t, _) ->
    let pat, nbind = gen_pat (env, id_spec) bind [] p in
    let term = gen_term (env, id_spec) default ((List.rev nbind)@bind) t in
    (List.map ml_id_of_ident nbind, pat, term)) ptl in
  MLcase (Tunknown, t, Array.of_list pats)
  | MLTALin cl -> 
    let cli = List.map (function ((MLTVar v1, _), (MLTVar v2, _)) -> v1, v2
      | _ -> assert false
    ) cl in
    let cl' = List.map (fun (c1, c2) -> 
      MLapp (MLglob (mk_dummy_glb (env, id_spec) (ident_of_string "(=)")),
        [MLrel (get_rel c1 bind); MLrel (get_rel c2 bind)])) cli in
    List.fold_left
      (fun t c -> MLapp (MLglob (mk_dummy_glb (env, id_spec) 
        (ident_of_string "(&&)")), [t; c]))
      (List.hd cl') (List.tl cl')
  | MLTADefault _ -> default
  | _ -> anomalylabstrm "RelationExtraction" (str "Unknown term in MiniML")


(* Gets the type of a constr. *)
let rec type_of_constr c =
  match kind_of_term c with
  | Const _ | Ind _ | Construct _ | Var _ -> Tglob (global_of_constr c, [])
  | App (h, a) ->
    Tglob (global_of_constr h, List.map type_of_constr (Array.to_list a))
  | Rel i -> Tvar i
  | _ -> assert false

(* Gets the type of a conclusion. *)
let rec type_of_concl mode prod = match mode, prod with
  | (MInput|MSkip)::modet, _::prodt -> type_of_concl modet prodt
  | MOutput::_, (_,c)::_ -> type_of_constr c
  | _ -> Tglob (bool_glb (), [])

(* Gets the type of a function. *)
let rec gen_type mode prod concl = match mode, prod with
  | MInput::modet, (_, c)::prodt -> 
      Tarr (type_of_constr c, gen_type modet prodt concl)
  | (MOutput|MSkip)::modet, _::prodt -> gen_type modet prodt concl
  | _ -> concl

(* Generates a function. *)
let gen_func args code = List.fold_left (fun code a -> MLlam (a, code))
  code (List.map ml_id_of_ident args)

(* Initializes the MiniML code generation. *)
let miniml_init =
  let init_done = ref false in
  fun () ->
    if not !init_done then
(*    let _ = Library.require_library 
        [(Util.dummy_loc, qualid_of_string "Coq.Bool.Bool")] (Some false) in *)
(*    let _ = Extract_env.simple_extraction (Qualid 
        (Util.dummy_loc, qualid_of_string "Coq.Init.Datatypes.bool")) in*)
(*      let _ = Printf.printf "(* Required by relation extraction. *)\n%s\n\n"
        "let ocaml_beq = fun x y -> if x = y then True else False" in*)
      let bool_ref = Libnames.Qualid 
        ((dummy_loc, qualid_of_string "Coq.Init.Datatypes.bool")) in
      let _ = Table.extract_inductive bool_ref "bool" ["true"; "false"] None in
      init_done := true;
      ()
    else ()

let is_full_extraction mode = List.for_all ((<>) MOutput) mode

(* Generates one MiniML function (ready to be printed). *)
let gen_miniml_func env (id, f) =
  let mode = List.hd (extr_get_modes env id) in
  let glb = get_indgref env id in
  let typ = Global.type_of_global glb in
  let (prod, _) = decompose_prod typ in
  let nprod = List.rev prod in
  let concl = type_of_concl mode nprod in 
  let mlt = gen_type mode nprod concl in
  let default = if is_full_extraction mode then
    get_false ()
  else
    MLexn "" in
  let args = List.rev f.mlfun_args in
  let code = gen_term (env, id) default args f.mlfun_body in
  let mla = gen_func args code in
  (* We can't generate a new reference each time because there must be
     only one reference of each id ... else it makes bugs. 
     TODO: verfiy that we really have one ref by id and find a good way
     to declare new ones (verify there existence in the extract env before
     generating references with mk_dummy_glb ?). *)
  let glb = (*mk_dummy_glb (env, id) f.mlfun_name in*)
            global_of_constr (get_cstr (env, id) f.mlfun_name) in
  (glb, mla, mlt)

let rec list_split3 l = match l with
  | [] -> [], [], []
  | (a, b, c)::t -> let al, bl, cl = list_split3 t in
    a::al, b::bl, c::cl

let add_cstr_to_env env id cstr =
  if List.mem_assoc id env.extr_henv.cstrs then env
  else let cstrs' = (id, cstr)::env.extr_henv.cstrs in
  {env with extr_henv = {env.extr_henv with cstrs = cstrs'}}
let add_fake_cstr_to_env (env, id_spec) id =
  let fake_gref = mk_dummy_glb (env, id_spec) id in
  add_cstr_to_env env id (constr_of_global fake_gref)


(* MiniML code generation. *)
let gen_miniml env = 
  let _ = miniml_init () in
  let funs = env.extr_mlfuns in
  let env = List.fold_right (fun (id, f) env -> add_fake_cstr_to_env (env, id)
              f.mlfun_name) funs env in
  let mlfuncs = List.map (gen_miniml_func env) funs in
  let glbs, mlas, mlts = list_split3 mlfuncs in
  let mld =
    Dfix (Array.of_list glbs, Array.of_list mlas, Array.of_list mlts) in
  let fn = string_of_ident (fst (List.hd funs)) in
  let id = fst (List.hd funs) in
  let glb = get_indgref env id in
  let lbl = mk_label fn in
  let mpt = modpath_of_r glb in
  let mls = [mpt, [lbl, SEdecl mld]] in 
  print_one_decl mls mpt mld
