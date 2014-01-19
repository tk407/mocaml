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

open Util
open Pp
open Declarations
open Term
open Names
open Libnames
open Nametab
open Inductive
open Pred
open Host_stuff
open Coq_stuff

(* TODO:
   - correct types annotations for (=) arguments.
     currently they are typed as "refl_eq".
*)

(* Adds the global reference of an inductive into the exract env. *)
let add_indgref_to_env env id ind_gref =
  if List.mem_assoc id env.extr_henv.ind_grefs then env
  else let ind_grefs' = (id, ind_gref)::env.extr_henv.ind_grefs in
  {env with extr_henv = {env.extr_henv with ind_grefs = ind_grefs'}}

(* Adds the global reference of an inductive into the exract env. *)
let add_cstr_to_env env id cstr =
  if List.mem_assoc id env.extr_henv.cstrs then env
  else let cstrs' = (id, cstr)::env.extr_henv.cstrs in
  {env with extr_henv = {env.extr_henv with cstrs = cstrs'}}

(* Gets the identifier of a binder *)
let get_name = function
  | (Name id, _) -> id
  | _ -> anomalylabstrm "RelationExtraction"
                        (str "Cannot find the name of a binder")

(* Finds a list of the constructors of an inductive type. *)
let find_it_constrs constr = 
  let ind, i = destConstruct constr in
  let _,idc = Inductive.lookup_mind_specif (Global.env ()) ind in
  List.map (fun cstr_id  -> 
    ident_of_string (string_of_id cstr_id)
  ) (Array.to_list idc.mind_consnames)

(* Gets type of one inductive body. *)
let get_prod_type_from_oib oib =
  match oib.mind_arity with
      | Monomorphic a -> a.mind_user_arity
      | _ -> errorlabstrm "RelationExtraction" (str "Non monomorphic arity")

(* TODO: make compatibility with mutual inductives (see the <Rel _> case) *)
(* Finds type of a constructor. For each argument of this constructor:
     - the list of constructors of the argument type.
     - the argument type itself. *)
let find_types_of_constr constr = match kind_of_term constr with
  | Construct (ind, i) -> 
    let mib, oib = Inductive.lookup_mind_specif (Global.env ()) ind in
    let (n, _) = decompose_prod oib.mind_user_lc.(i-1) in
    List.map (fun (_, c) -> match kind_of_term c with
      | Ind ind ->
        let _, oib = Inductive.lookup_mind_specif (Global.env ()) ind in
        CTSum (List.map (fun cstr_id  -> 
          (ident_of_string (string_of_id cstr_id))
        ) (Array.to_list oib.mind_consnames)), Some c
      | Rel _ -> let ty = mkInd ind in
        let _, oib = Inductive.lookup_mind_specif (Global.env ()) ind in
        CTSum (List.map (fun cstr_id  -> 
          (ident_of_string (string_of_id cstr_id))
        ) (Array.to_list oib.mind_consnames)), Some ty
      | _ -> CTNone, Some c
    ) (List.rev n)
  | _ -> anomalylabstrm "RelationExtraction" (str "Constructor type not found")

(* TODO: make compatibility with mutual inductives (see the <Rel _> case) *)
(* Finds type of an inductive arguments. For each argument:
     - the list of constructors of the argument type.
     - the argument type itself. *)
let find_types_of_ind ind = 
  let _, oib = Inductive.lookup_mind_specif (Global.env ()) ind in
  let (n, _) = decompose_prod (get_prod_type_from_oib oib) in
    List.map (fun (_, c) -> match kind_of_term c with
      | Ind ind ->
        let _, oib = Inductive.lookup_mind_specif (Global.env ()) ind in
        CTSum (List.map (fun cstr_id  -> 
          (ident_of_string (string_of_id cstr_id))
        ) (Array.to_list oib.mind_consnames)), Some c
      | Rel _ -> let ty = mkInd ind in
        let _, oib = Inductive.lookup_mind_specif (Global.env ()) ind in
        CTSum (List.map (fun cstr_id  -> 
          (ident_of_string (string_of_id cstr_id))
        ) (Array.to_list oib.mind_consnames)), Some ty
      | _ -> CTNone, Some c
    ) (List.rev n)


let rec filter2 p l1 l2 = match l1, l2 with
  | a::tl1, b::tl2 -> if p a b then let l1, l2 = filter2 p tl1 tl2 in
      a::l1, b::l2
    else filter2 p tl1 tl2
  | _ -> l1, l2
let rec filter3 p l1 l2 l3 = match l1, l2, l3 with
  | a::tl1, b::tl2, c::tl3 -> if p a then let l2, l3 = filter3 p tl1 tl2 tl3 in
      b::l2, c::l3
    else filter3 p tl1 tl2 tl3
  | _ -> l2, l3
let rec map_filter f l = match l with
  | [] -> []
  | a::tl -> let b, a' = f a in if b then 
      a'::(map_filter f tl) 
    else map_filter f tl

(* Filters implicit arguments of Coq constr arguments.
   h and args must come from a constr of the form App(h, args).
   When typs is not known, the function can be called with h args args. *)
let filter_impargs_cstr h args typs =
  let imp = match Impargs.implicits_of_global (global_of_constr h) with
    | (_,a)::_ -> a
    | _ -> [] in
  let filter = fun a -> not (Impargs.is_status_implicit a) in
  let rec terms_filter term typ = match kind_of_term term with
    | Ind _ -> false
    | App (h, _) -> terms_filter h typ
    | _ -> true in
  let args = Array.to_list args in
  let no_imp_args, no_imp_typ =
    if List.length args <> List.length imp then args, typs
    else filter3 filter imp args typs in
  let nargs, ntyps = filter2 terms_filter no_imp_args no_imp_typ in
  (Array.of_list nargs, ntyps)

(* Parses a simple Coq term. *)
let rec build_untyped_term (env, id_spec) prod term = 
match kind_of_term term with
  | Const c -> let i = ident_of_string (string_of_con c) in
    let env = add_cstr_to_env env i term in
    MLTConst i, env
  | Rel i -> let n = 
    ident_of_string (string_of_id (get_name (List.nth prod (i-1)))) in
    MLTVar n, env
  | App (h, args) when isConstruct h ->
    let typs = find_types_of_constr h in
    let args, typs = filter_impargs_cstr h args typs in
    let _, i = destConstruct h in
    let it_constrs = find_it_constrs h in
    let constr = List.nth it_constrs (i-1) in
    let args, env = List.fold_right2 (fun t a (args, env) ->
      let a, env = build_term (env, id_spec) prod (Some t) a in
      a::args, env) typs (Array.to_list args) ([], env) in 
    let env = add_cstr_to_env env constr h in
    MLTConstr (constr, args), env
  | Construct _ ->
    let ind, i = destConstruct term in
    let it_constrs = find_it_constrs term in
    let constr = List.nth it_constrs (i-1) in
    (* Add all the constructors to env. *)
    let env, _ = List.fold_left (fun (env, i) constr ->
      let construct = mkConstruct (ind, i) in
      (add_cstr_to_env env constr construct, i+1)
    ) (env, 1) it_constrs in
(*    let env = add_cstr_to_env env constr term in*)
    MLTConstr (constr, []), env
  | App (h, args) -> 
    let args, _ = filter_impargs_cstr h args (Array.to_list args) in
    let c = destConst h in
    let n = con_label c in
    let s = ident_of_string (string_of_label n) in
    let args, inf = List.fold_right (fun a (args, env) ->
      let a, env = build_term (env, id_spec) prod None a in
      a::args, env) (Array.to_list args) ([], env) in
    let env = add_cstr_to_env env s h in
    MLTFun (s, args, None), env
  | _ -> anomalylabstrm "RelationExtraction" (str "Unknown Coq construction")
and build_term (env, id_spec) prod typ term = 
  let (t, env) = build_untyped_term (env, id_spec) prod term in
  match typ with
    | None -> fake_type env t, env
    | Some typ -> (t, typ), env

(* Mode Skip filter *)
let rec filter_mode_skip mode args = match (mode, args) with
  | (MSkip::tl_mode, a::tl_args) -> filter_mode_skip tl_mode tl_args
  | (_::tl_mode, a::tl_args) -> a::(filter_mode_skip tl_mode tl_args)
  | _ -> []


(* Parses the conclusion of a predicate's constructor (or property). *)
let build_concl (env, id_spec) named_prod term = match kind_of_term term with
  | App (_, args) -> let mode = List.hd (extr_get_modes env id_spec) in
    let ind_ref = List.assoc id_spec env.extr_henv.ind_refs in
    let ind = destInd (constr_of_global (global ind_ref)) in
    let typs = find_types_of_ind ind in
    let args = filter_mode_skip mode (Array.to_list args) in
    let typs = filter_mode_skip mode typs in
    let args, env = List.fold_right2 (fun a t (args, env) ->
      let a, env = build_term (env, id_spec) named_prod (Some t) a in
      a::args, env
    ) args typs ([], env) in
    fake_type env (MLTFun (id_spec, args, Some mode)), env
  | _ -> anomalylabstrm "RelationExtraction"
                        (str "Cannot find a constructor's conclusion")

(* Tests if a constr is \/ *)
let isOr constr =
  if isInd constr then
    let ind = destInd constr in
    let _,oid = Inductive.lookup_mind_specif (Global.env ()) ind in
    (string_of_id oid.mind_typename = "or")
  else false

(* Tests if a constr is /\ *)
let isAnd constr =
  if isInd constr then
    let ind = destInd constr in
    let _,oid = Inductive.lookup_mind_specif (Global.env ()) ind in
    (string_of_id oid.mind_typename = "and")
  else false

(* Tests if a constr is not *)
let isNot constr =
  if isConst constr then
    let c = destConst constr in
    let str = string_of_con c in
    let str' = try let i = String.rindex str '#' in
      String.sub str (i+1) (String.length str - i - 1)
    with Not_found | Invalid_argument _ -> str in
    str' = "not" || str' = "Coq.Init.Logic.not"
  else false

(* Parses a premisse of a predicate's constructor (or property). *)
let rec build_premisse (env, id_spec) named_prod term =
  let build_predicate ind args = 
    let _, oib = Inductive.lookup_mind_specif (Global.env ()) ind in
    let ind_gref = locate (qualid_of_ident oib.mind_typename) in
    let id = ident_of_string (string_of_id oib.mind_typename) in
    let modes = begin match extr_get_modes env id with
      | [] -> [make_mode ind_gref None]
      | modes -> modes end in
    let typs = find_types_of_ind ind in
    let pred_terms, env = List.fold_right (fun mode (pred_terms, env) ->
      let args = filter_mode_skip mode (Array.to_list args) in
      let typs = filter_mode_skip mode typs in
      let args, env = List.fold_right2 (fun a t (args, env) ->
        let a, env = build_term (env, id_spec) named_prod (Some t) a in
        a::args, env
      ) args typs ([], env) in
      (* A premisse term must be typed with its output type (for fixpred). 
         If there are several outputs, we use a fake type. *)
      let prem_term = MLTFun (id, args, Some mode) in
      let prem_term_type = match get_out_terms_func env 
        (fake_type env prem_term) with
        | [t, ty] -> ty
        | [] ->
          (CTSum [ident_of_string "true";ident_of_string "false"], 
            Some (constr_of_global 
              (locate (qualid_of_string "Coq.Init.Datatypes.bool"))))
        | _ -> unknown_type env in
      (PMTerm ((prem_term, prem_term_type), Some (fresh_ident "Pm_" ())))::pred_terms, env
    ) modes ([], env) in
    let env = add_indgref_to_env env id ind_gref in
    begin match pred_terms with
      | [] -> anomalylabstrm "RelationExtraction" (str "Bad premisse form")
      | [pred_term] -> pred_term, env
      | _ -> PMChoice (pred_terms, Some (fresh_ident "Pm_" ())), env 
    end in
  begin match kind_of_term term with
    | App (h, [|arg|]) when isNot h ->
      let pm, env = build_premisse (env, id_spec) named_prod arg in
      (PMNot (pm, Some (fresh_ident "Pm_" ())), env)
    | App (h, args) when isOr h ->
      let pms, env = build_premisse_list (env, id_spec) 
        named_prod (Array.to_list args) in
      (PMOr (pms, Some (fresh_ident "Pm_" ())), env)
    | App (h, args) when isAnd h ->
      let pms, env = build_premisse_list (env, id_spec) 
        named_prod (Array.to_list args) in
      (PMAnd (pms, Some (fresh_ident "Pm_" ())), env)
    | App (h, _) when isConst h -> let t, env = build_term (env, id_spec) 
        named_prod None term in
      PMTerm (t, Some (fresh_ident "Pm_" ())), env
    | App (h, args) when isInd h -> let ind = destInd h in
      build_predicate ind args
    | App (h, args) when isRel h -> let i = destRel h in
      let ind_ref = List.assoc id_spec env.extr_henv.ind_refs in
      let ind = destInd (constr_of_global (global ind_ref)) in
      let mib, oib = Inductive.lookup_mind_specif (Global.env ()) ind in
      let ind_binds = List.rev (Array.to_list mib.mind_packets) in
      let i = i - List.length named_prod - 1 in
      let good_oib = List.nth ind_binds i in
      let ind_gref = global (Ident (dummy_loc, good_oib.mind_typename)) in
      let ind = destInd (constr_of_global ind_gref) in
      build_predicate ind args
    | _ -> anomalylabstrm "RelationExtraction" (str "Bad premisse form")
  end

and build_premisse_list (env, id_spec) named_prod terms =
  List.fold_right (fun term (prems, env) ->
    let p, env = build_premisse (env, id_spec) named_prod term in
    p::prems, env
  ) terms ([], env)

let build_prem (env, id_spec) named_prod cstr = match kind_of_term cstr with
  | App (_, args) ->
    let t, env = build_premisse (env, id_spec) named_prod cstr in
    begin match t with
      | PMTerm ((MLTFun (_, [], _),_),_) ->
        ([], env) (* fix for the fake list() premisse *)
      | _ -> ([t], env)
    end
  | _ -> ([], env)

(* Parses the whole set of premisses of a predicate's constructor
   (or property). *)
let rec build_prems (env, id_spec) named_prod cstr_list = match cstr_list with
  | [] -> [], env
  | cstr::tail -> if isProd cstr then
    anomalylabstrm "RelationExtraction" (str "Too many products in a premisse")
  else
    let p, env = build_prem (env, id_spec) (List.tl named_prod) cstr in
    let p2, env = build_prems (env, id_spec) (List.tl named_prod) tail in
    (p@p2, env)


(* Parses a predicate's constructor (or property). *)
let build_prop (env, id_spec) prop_name prop_type =
  let named_prod, concl = decompose_prod prop_type in
  let concl, env = build_concl (env, id_spec) named_prod concl in
  let named_prems = List.filter (fun (x, _) -> x = Anonymous) named_prod in
  let prems = List.map snd named_prems in
  let prems, env = build_prems (env, id_spec) named_prod prems in
  let vars = map_filter (fun (x, _) -> match x with 
    | Name id -> true, ident_of_string (string_of_id id)
    | Anonymous -> false, ident_of_string "") named_prod in
  {
    prop_name = Some prop_name;
    prop_vars = vars;
    prop_prems = prems;
    prop_concl = concl
  }, env

  
(* Parses one predicate's specification. *)
let find_one_spec env (id_spec, _) =
  let idr = List.assoc id_spec env.extr_henv.ind_refs in
  let ind = destInd (constr_of_global (global idr)) in
  let _, oib = Inductive.lookup_mind_specif (Global.env ()) ind in
  let props, env = List.fold_right2 (fun prop_name cstr (pl, env) -> 
      let prop_name = ident_of_string (string_of_id prop_name) in
      let p, env = build_prop (env, id_spec) prop_name cstr in
      p::pl, env
    )
    (Array.to_list oib.mind_consnames)
    (Array.to_list oib.mind_user_lc) ([], env) in
  let args_types = find_types_of_ind ind in
  (id_spec, {
    spec_name = id_spec;
    spec_args_types = args_types;
    spec_props = props;
  }), env


let find_specifications env = 
  let specs, env = List.fold_right (fun e (specs, env) ->
    let s, env = find_one_spec env e in
    s::specs, env) env.extr_extractions ([], env) in
  { env with extr_specs = specs }

