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
open Fixpred
open Coq_stuff
open Minimlgen
open Proofgen

open Term
open Names
open Declarations
open Libnames
open Nametab
open Command
open Decl_kinds
open Util
open Pp


(* Is a coq constr the option type ? *)
let is_ind_type_option c = match kind_of_term c with
  | Ind ind -> 
    let _,oib = Inductive.lookup_mind_specif (Global.env ()) ind in
    string_of_id oib.mind_typename = "option"
  | _ -> false


(* sty is an inductive coq type. Returns a list which contains the types
   of arguments of each constructor of sty (ie a so_term_type list list). *)
let rec find_args_types sty = match kind_of_term sty with
  | App (c, [|t|]) when is_ind_type_option c -> 
    (* hack: args of option type without the parameter. *)
    [[t];[]] (* Some and None *)
  | App (c, _) -> find_args_types c
  | Ind ind -> 
    let mib,oib = Inductive.lookup_mind_specif (Global.env ()) ind in
    let constrs = Array.to_list oib.mind_user_lc in
    List.map ( fun t ->
      let (n, _) = decompose_prod t in
      List.flatten (List.map (fun (_,c) -> match kind_of_term c with
        | Ind _ -> [c]
        | Rel _ -> [sty]
        | _ -> [] (* hack to support the first argument of type option. *)
      ) (List.rev n))
    ) constrs
  | _ -> anomalylabstrm "RelationExtraction" (str "Not an inductive type")



(* Gets the parameter type of an option type. *)
let extract_type_from_option ctyp = match kind_of_term ctyp with
  | App (_, [|ty|]) -> ty
  | _ -> assert false

(* Generates a Coq Constr. *)
let rec gen_constr (env, id) fn bind (fterm,_) = match fterm with
  | FixVar i -> mkRel (Minimlgen.get_rel i bind)
  | FixConstr (i, [t,(ty,Some cty)]) when string_of_ident i = "Some" -> 
    let some = constr_of_global 
      (locate (qualid_of_string "Coq.Init.Datatypes.Some")) in
    let args = Array.of_list 
      [cty ; (gen_constr (env, id) fn bind (t,(ty,Some cty)))] in
    mkApp (some, args)
  | FixConstr (i, []) when string_of_ident i = "None" -> 
    let none = constr_of_global 
      (locate (qualid_of_string "Coq.Init.Datatypes.None")) in
    let args = Array.of_list 
      [(* debug TODO: not always out_type ?*) get_out_type false (env, id)] in
    mkApp (none, args)
  | FixConstr (i, tl) -> 
    let c = List.assoc i (env.extr_henv.cstrs) in
    let args = Array.of_list (List.map (gen_constr (env,id) fn bind) tl) in
    mkApp (c, args)
  | FixConst i -> List.assoc i (env.extr_henv.cstrs)
  | FixFun (i, tl) -> 
    let c = if i = fn then mkRel (List.length bind + 1)
            else try List.assoc i (env.extr_henv.cstrs) with Not_found -> 
      constr_of_global (Nametab.global 
        (Ident (Util.dummy_loc, id_of_string (string_of_ident i)))) in
    let args = Array.of_list (List.map (gen_constr (env,id) fn bind) tl) in
    mkApp (c, args)
  | FixFunNot _ -> 
    anomalylabstrm "RelationExtraction" (str "Not: Not implanted yet")
  | FixCase ((_, (_, Some sty)) as t, _, iltl) -> 
    let ind, oib = match kind_of_term sty with
      | App (c,_) -> (match kind_of_term c with
        | Ind ind -> 
          let _,oib = Inductive.lookup_mind_specif (Global.env ()) ind in
          ind, oib )
      | Ind ind  ->
        let _,oib = Inductive.lookup_mind_specif (Global.env ()) ind in
        ind, oib
      | _ -> assert false in
    let npar = if string_of_id oib.mind_typename = "option" then 1 else 0 in
      (* The option type has one parameter. 
         TODO: support parameters in other inductives. *)
    let args_nb = List.map (fun (il, _, _) -> List.length il) iltl in
    let args_tab = Array.of_list args_nb in
    let case_inf = { 
      ci_ind = ind;
      ci_npar = npar;
      ci_cstr_ndecls = args_tab;
      ci_pp_info = { ind_nargs = 0;
                     style = MatchStyle }
    } in
    let cstrs_arg_types = find_args_types sty in
    let ty = mkLambda (Anonymous, sty, (get_out_type true (env,id))) in
    let ta = Array.of_list (List.map2 (fun (il, t, _) tyl ->
      let nbind = (List.rev il) @ bind in
      List.fold_right2 (fun i ty t -> 
        mkLambda (Name (id_of_string (string_of_ident i)), ty, t)
      ) il tyl (gen_constr (env,id) fn nbind t)  
    ) iltl cstrs_arg_types) in
    mkCase (case_inf, ty, (gen_constr (env,id) fn bind t), ta)
  | FixCase _ -> anomalylabstrm "RelationExtraction" 
    (str "Missing type information in pattern matching")
  | FixSome (t,(ty,Some cty)) -> let some = constr_of_global 
    (locate (qualid_of_string "Coq.Init.Datatypes.Some")) in
    let args = Array.of_list 
               [cty ; (gen_constr (env,id) fn bind (t,(ty,Some cty)))] in
    mkApp (some, args)
  | FixNone -> let non = constr_of_global 
    (locate (qualid_of_string "Coq.Init.Datatypes.None")) in
    mkApp (non, [|get_out_type false (env,id)|])
  | FixTrue -> constr_of_global 
    (locate (qualid_of_string "Coq.Init.Datatypes.true"))
  | FixFalse -> constr_of_global
    (locate (qualid_of_string "Coq.Init.Datatypes.false"))
  | FixLetin (i, (l,(ty, Some sty)), t, _) ->
    mkLetIn (Name (id_of_string (string_of_ident i)), 
      (gen_constr (env,id) fn bind (l,(ty, Some sty))), sty,
      (gen_constr (env,id) fn (i::bind) t))
  | FixLetin _ -> anomalylabstrm "RelationExtraction" 
    (str "Missing type information in let in")

(* Generates the type of an extracted function. *)
let gen_fix_type (env,id) args =
  let in_types = get_in_types (env, id) in
  let out_type = get_out_type true (env, id) in
  List.fold_right2 ( fun at an typs -> 
    mkProd (Name (id_of_string an), get_coq_type at, typs) 
  ) in_types args out_type


(* Generates and registers Coq Fixpoints. *)
let gen_fixpoint_bis env =
  let glbs = List.map (fun (i, (f, _)) ->
    let (fn, args, t) = f.fixfun_name, f.fixfun_args, f.fixfun_body in
    let c = gen_constr (env,i) fn (List.rev args) t in
    let typs = get_in_types (env, i) in
    let c = List.fold_right2 ( fun a t c -> 
      mkLambda (Name (id_of_string a), get_coq_type t, c) ) 
      (List.map string_of_ident args) typs c in
    let ty = gen_fix_type (env,i) (List.map string_of_ident args) in
    let recdec = 
      ([|(Name (id_of_string (string_of_ident fn)))|], [|ty|], [|c|]) in
    let fi = match fix_get_recursion_style env i with
      | StructRec i -> ([|i-1|], 0), recdec 
      | _ -> ([|0|], 0), recdec in
    let f = mkFix fi in
    declare_fix Fixpoint (id_of_string (string_of_ident fn)) f ty []
  ) env.extr_fixfuns in 
  let glb = List.hd glbs in
  let cstr = constr_of_global glb in
  let cst = destConst cstr in
  let cst_body = Global.lookup_constant cst in
  let cstr = match cst_body.Declarations.const_body with 
  | Def cs -> Declarations.force cs in

  (* Proofs generation *)
  let _ = List.iter (fun (id, _) -> gen_correction_proof env id) 
    env.extr_fixfuns in
  ()

(* Generates and registers Coq Fixpoints. *)
let gen_fixpoint env = 
  let _ = gen_fixpoint_bis env in ()


