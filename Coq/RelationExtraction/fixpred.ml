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
open Host_stuff
open Minimlgen
open Proof_scheme

open Term
open Names
open Declarations
open Util
open Pp
open Nametab
open Libnames

exception RelExtNoFixTuple
exception RelExtImcompleteFunction

let flatmap f l = List.flatten (List.map f l)


(* Pattern matching compilation *)

(* Renames the term if i is not present in the pattern. *)
let rec rename_var_pattern oi ni (p, ty) = match p with
  | MLPVar vi when vi = oi -> MLPVar ni, ty
  | MLPTuple pl -> MLPTuple (List.map (rename_var_pattern oi ni) pl), ty
  | MLPRecord (il, pl) -> 
    MLPRecord (il, List.map (rename_var_pattern oi ni) pl), ty
  | MLPConstr (i, pl) -> 
    MLPConstr (i, List.map (rename_var_pattern oi ni) pl), ty
  | _ -> p, ty

(* Renames a variable in a term. *)
let rec rename_var_term oi ni (t, ty) = match t with
  | MLTVar vi when vi = oi -> MLTVar ni, ty
  | MLTASome t -> MLTASome (rename_var_term oi ni t), ty
  | MLTTuple tl -> MLTTuple (List.map (rename_var_term oi ni) tl), ty
  | MLTRecord (il, tl) -> 
    MLTRecord (il, List.map (rename_var_term oi ni) tl), ty
  | MLTConstr (i, tl) -> MLTConstr (i, List.map (rename_var_term oi ni) tl), ty
  | MLTFun (i, tl, m) -> MLTFun (i, List.map (rename_var_term oi ni) tl, m), ty
  | MLTFunNot (i, tl, m) -> 
    MLTFunNot (i, List.map (rename_var_term oi ni) tl, m), ty
  | MLTMatch (t, an, ptl) -> MLTMatch (rename_var_term oi ni t, an,
    List.map (fun (p,t,an) -> 
      rename_var_pattern oi ni p, rename_var_term oi ni t, an) ptl), ty
  | MLTALin _ -> anomalylabstrm "RelationExtraction" (str "Not implanted yet")
  | _ -> t, ty

(* Extracts the first column of a patterns matrix. *)
let rec extract_one_col pltl = match pltl with
  | [] -> [], []
  | (p::pl_tail, t, an)::pltl_tail -> 
    let col, npltl = extract_one_col pltl_tail in
    p::col, (pl_tail,t,an)::npltl
  | _ -> assert false


(* Merges a column into a patterns matrix. *)
let merge_col pl pltl = List.map2 (fun p (pl, t, an) -> p::pl, t, an) pl pltl
(* Same function but with list of patterns in the "column". *)
let merge_cols pll pltl = 
  List.map2 (fun pl2 (pl, t, an) -> pl2@pl, t, an) pll pltl

(* Explodes tuples into a patterns matrix. *)
let rec normalize_pltl_tuples tl pltl = match tl with
  | (MLTTuple tup, _)::tl_tail -> let ntl = tup@tl_tail in
    let tuple_col, npltl = extract_one_col pltl in
    let ncols = List.map (function
      | MLPTuple pl, _ -> pl
      | _ -> raise RelExtNoFixTuple
    ) tuple_col in
    let npltl = merge_cols ncols npltl in
    normalize_pltl_tuples ntl npltl
  | t::tl_tail -> let col, pltl_tail = extract_one_col pltl in
    let ntl, npltl = normalize_pltl_tuples tl_tail pltl_tail in
    t::ntl, merge_col col npltl
  | [] -> tl, pltl

(* pltl is a pattern matrix with a list of patterns and a term in each row.
 After normalization, each row must have the same number of pattern as tl 
 and must not contain any tuple. 
 If there is a default case, it is removed. *)
let rec normalize_pltl tl pltl =
  let npltl = List.filter (fun (pl, t, an) ->
    List.for_all (function MLPWild, _ -> false | _ -> true) pl
  ) pltl in
  normalize_pltl_tuples tl npltl

(* Generates the default case (None or False). *)
let gen_default_case env mode = 
  if is_full_extraction mode then fake_type env FixFalse
  else fake_type env FixNone

(* Makes a list of n fresh variables. *)
let rec make_cstr_pat_vars n =
  if n = 0 then [] 
  else (ident_of_string (fresh_string_id "fix_" ())) :: 
    (make_cstr_pat_vars (n-1))

(* Makes a list of n wild patterns. *)
let rec make_wild_pats env n =
  if n = 0 then [] else (fake_type env MLPWild) :: (make_wild_pats env (n-1))

(* Gets the type from a product. *)
let typ_from_named env ind (_,c) = match kind_of_term c with
  | Ind ind ->
    let _,idc = Inductive.lookup_mind_specif (Global.env ()) ind in
    CTSum (List.map (fun cstr_id  -> 
      (ident_of_string (string_of_id cstr_id))
    ) (Array.to_list idc.mind_consnames)), Some c (* c is the type of idc *)
  | Rel _ -> let ty = mkInd ind in
    let _,oib = Inductive.lookup_mind_specif (Global.env ()) ind in
    CTSum (List.map (fun cstr_id  -> 
      (ident_of_string (string_of_id cstr_id))
    ) (Array.to_list oib.mind_consnames)), Some ty
  | _ -> unknown_type env

(* Filters l2 with p applied on l1. *)
let rec filter2 p l1 l2 = match l1, l2 with
  | a::tl1, b::tl2 -> if p a then let l2 = filter2 p tl1 tl2 in
      b::l2
    else filter2 p tl1 tl2
  | _ -> l2

(* Finds the Coq type of constr *)
let coq_type_explorer env cstr = match kind_of_term cstr with
  | Construct (ind, i) ->
    let mib,oib = Inductive.lookup_mind_specif (Global.env ()) ind in
    let (n, _) = decompose_prod oib.mind_user_lc.(i-1) in
    let n = List.map (typ_from_named env ind) (List.rev n) in
(*basic imp args filter, TODO: unification with the host2spec algorithm ?*)
    let imp = match Impargs.implicits_of_global (
        Libnames.global_of_constr cstr) with
      | (_,a)::_ -> a
      | _ -> [] in
    let filter = fun a -> not (Impargs.is_status_implicit a) in
    let n = if List.length n <> List.length imp then n
      else filter2 filter imp n in
(*end*)
    List.length n, n
  | _ -> assert false

(* Finds the list of constructors of a coq inductive type. *)
let clear_type_from_coq typ = match kind_of_term typ with
  | Ind ind -> 
    let _,oib = Inductive.lookup_mind_specif (Global.env ()) ind in
    let cstrs_names = List.map (fun n -> ident_of_string (string_of_id n))
      (Array.to_list oib.mind_consnames) in
    CTSum cstrs_names

(* Gets the arity and types of the arguments of a constructor by searching it 
 in the first column of a patterns matrix. 
 If the constructor is not present in the first column, tries to find it using
 the cstr's id and the spec. *)
(* TODO: better handle for the case : (0, []), done ?*)
let rec get_cstr_arity_and_types env cstr pltl = match pltl with
  | [] -> let cstr = try List.assoc cstr env.extr_henv.cstrs with Not_found -> 
      try find_coq_constr_i cstr with Not_found -> (*TODO:this line is a 
                                         temporary fix for bst in full mode *)
      anomalylabstrm "RelationExtraction" 
      (str ("Cannot find the '" ^ string_of_ident cstr ^ 
            "' constructor in the extraction environment")) in
    coq_type_explorer env cstr
  | ((MLPConstr (c, args), _)::_, _, _)::_ when c = cstr ->
    (List.length args, List.map snd args)
  | _::pltl_tail -> get_cstr_arity_and_types env cstr pltl_tail

(* filtering useless cases *)
let filter_next_pats pltl tl = 
  let rec filter_pll pll tl = match tl with
    | [] -> pll, tl
    | t::tl_tail -> try 
      let npll, ntl = filter_pll (List.map List.tl pll) tl_tail in
      if List.for_all (function | (MLPWild, _)::_ -> true | _ -> false) pll then 
        npll, ntl
      else List.map2 (fun pl npl -> (List.hd pl)::npl) pll npll, t::ntl 
    with _ -> assert false in
  let filtered_pll, ntl = 
    filter_pll (List.map (fun (pl, t, an) -> pl) pltl) tl in
  (List.map2 (fun pl (_,t,an) -> pl, t, an) filtered_pll pltl, ntl)

(* Compiles a normalized pattern matching. *)
let rec compile_fix_match comp (env, id_fun) binded_vars tl pltl = match tl with
  | [] -> begin match pltl with
    | [[], t, _] -> build_fix_term comp (env, id_fun) binded_vars t
               (* no more terms to match *)
    | ([], t, _)::_ -> 
             (* This happens in the relaxed extraction, we keep only the first
                output term. Most general pattens are always placed after. *)
          build_fix_term comp (env, id_fun) binded_vars t
  end
  | (mt, ((CTSum cstr_list, _) as mt_ty))::tl_tail ->
    (* match mt with the first pattern of every pl present in pltl *)

    (* are there any variables or constructors in the patterns ? *)
    let is_variables = List.exists (fun (pl, _, _) -> match pl with 
      | p::_ -> (match p with | MLPVar _, _ -> true | _ -> false)
      | _ -> assert false) pltl in
    let is_constrs = List.exists (fun (pl, _, _) -> match pl with 
      | p::_ -> (match p with | MLPConstr _, _ -> true | _ -> false)
      | _ -> assert false) pltl in
    let an = flatmap (fun (_, _, an) -> an) pltl in
    let nmt, lams, npltl = if is_variables then 
        let nvar = ident_of_string (fresh_string_id "fix_" ()) in
        (* if there is at least one variable: we create a variable for 
                                                                    the letin *)
        let npltl = List.map ( fun (pl, t, an) -> match pl with
          | (MLPVar v, vty)::pl_tail -> 
                (MLPWild, vty)::pl_tail, rename_var_term v nvar t, an
          (* then we replace each occurence of the variables by the 
             letin variable; v is no longer needed -> replaced by MLPWild *)
          | _ -> pl, t, an
        ) pltl in
        ( build_fix_term comp (env, id_fun) binded_vars (MLTVar nvar, mt_ty),
          (* The pattern matching is done on the letin var to avoid 
                                                            multiple calculi. *)
          [nvar, build_fix_term comp (env, id_fun) binded_vars (mt, mt_ty)],
          npltl )
      else 
        (build_fix_term comp (env, id_fun) binded_vars (mt, mt_ty)), [], pltl in
    let anlams = flatmap (fun (pl, _, an) -> match pl with
      | (MLPVar _, _)::_ -> an
      | _ -> []
    ) pltl in
    let anwild = flatmap (fun (pl, _, an) -> match pl with
      | (MLPWild _, _)::_ -> an
      | _ -> []
    ) pltl in
    let ancstrs = flatmap (fun (pl, _, an) -> match pl with
      | (MLPConstr _, _)::_ -> an
      | _ -> []
    ) pltl in

    let nterm = if is_constrs then
      let pats = List.map (fun cstr -> (* one pattern for each constr *)
        let cstr_arity, args_types = get_cstr_arity_and_types env cstr npltl in
        let wild_pats = make_wild_pats env cstr_arity in
        (* pat_vars will be used as arguments in the pattern. *)
        let pat_vars = make_cstr_pat_vars cstr_arity in
        (* next_pats will be added to the patterns matrix. *)
        let next_pats = flatmap (fun (pl, t, an) -> match pl with
          | (MLPConstr (c, args), ty)::pl_tail when c = cstr ->
            (* when an argument is a var, it is replaced by the pat_var;
               when it is a contr, it is left untouched. *)
            [List.fold_right2 (fun (a, ty) pv (pl, t, an) -> match a with
              | MLPVar v -> ((MLPWild, ty)::pl, rename_var_term v pv t, an)
              | _ -> ((a, ty)::pl, t, an)
            ) args pat_vars (pl_tail, t, an)]
          | (MLPWild, ty)::pl_tail -> [(wild_pats@pl_tail, t, an)]
          | _ -> []
        ) npltl in
        let ntl = (List.map2 (fun v ty -> 
          (MLTVar v, ty)) pat_vars args_types)@tl_tail in
        (* filter patterns for which we have only wildcards. *)
        let next_pats, ntl = filter_next_pats next_pats ntl in

        (* filter annotations, the cstr wust be in the pattern *)
        let ancstr = flatmap (fun (pl, _, an) -> match pl with
          | (MLPConstr (c, _), _)::_ when c = cstr -> an
          | _ -> []
        ) npltl in

        if List.length next_pats = 0 then
          (* TODO: if full extraction => false *)
          if is_full_extraction (List.hd (extr_get_modes env id_fun)) then
            (pat_vars, gen_default_case env 
              (List.hd (extr_get_modes env id_fun)), ancstr@anwild@anlams)
          else if comp then 
            (pat_vars, gen_default_case env 
              (List.hd (extr_get_modes env id_fun)), ancstr@anwild@anlams)
          else raise RelExtImcompleteFunction
        else
          (pat_vars, compile_fix_match comp 
            (env, id_fun) binded_vars ntl next_pats, ancstr@anwild@anlams)
      ) cstr_list in
      (FixCase (nmt, ancstrs, pats), (CTNone, None))

      else (* only variables: no pattern matching needed *)
        let ntl = List.tl tl in
        let _, npltl = extract_one_col npltl in
        compile_fix_match comp (env, id_fun) binded_vars ntl npltl in
      List.fold_right (fun (i, l) t -> 
        FixLetin (i, l, t, anlams), (CTNone, None)) lams nterm


  | (mt, ((_, _) ))::_ -> anomalylabstrm "RelationExtraction"
                                 (str "Missing type information")



(* Builds a fix_term, destructuring complex pattern matchings. *)
and build_fix_term c (env, id_fun) binded_vars (t,ty) = match t with
(* TODO: check if there are renaming matches, if not, add the Some constr. *)
  | MLTVar i -> FixVar i, ty
  | MLTTuple tl -> raise RelExtNoFixTuple
  | MLTConstr (i, tl) -> 
    FixConstr (i, List.map (build_fix_term c (env, id_fun) binded_vars) tl), ty
  | MLTConst i -> FixConst i, ty
  | MLTFun (i, tl, _) -> 
    FixFun (i, List.map (build_fix_term c (env, id_fun) binded_vars) tl), ty
  | MLTFunNot (i, tl, _) -> 
    FixFunNot (i, List.map (build_fix_term c (env, id_fun) binded_vars) tl), ty
  | MLTMatch (t, _, ptl) ->
    let tl, pltl = normalize_pltl 
      [t] (List.map (fun (p, t, an) -> [p], t, an) ptl) in
    compile_fix_match c (env, id_fun) binded_vars tl pltl
  | MLTALin _ -> anomalylabstrm "RelationExtraction" (str "Not implanted yet")
  | MLTATrue -> FixTrue, ty
  | MLTAFalse -> FixFalse, ty
  | MLTANone -> FixNone, ty
  | MLTASome t -> FixSome (build_fix_term c (env, id_fun) binded_vars t), ty
  | MLTADefault -> 
    if is_full_extraction (List.hd (extr_get_modes env id_fun)) then 
      fake_type env FixFalse
    else fake_type env FixNone
  | _ -> anomalylabstrm "RelationExtraction" (str "Not implanted yet")


(* Transform added pattern constrs (the ones with an A) to basic pattern
   constrs. *)
let rec transform_pat_constrs (lpat, ty) = match lpat with
  | MLPTuple pl -> MLPTuple (transform_pat_constrs_list pl), ty
  | MLPRecord (il, pl) -> MLPRecord (il, transform_pat_constrs_list pl), ty
  | MLPConstr (i, pl) -> MLPConstr (i, transform_pat_constrs_list pl), ty
  | MLPATrue -> MLPConstr (ident_of_string "true", []), 
    (CTSum [ident_of_string "true";ident_of_string "false"], 
     Some (constr_of_global 
       (locate (qualid_of_string "Coq.Init.Datatypes.bool"))))
  | MLPAFalse -> MLPConstr (ident_of_string "false", []), 
    (CTSum [ident_of_string "true";ident_of_string "false"], 
      Some (constr_of_global
        (locate (qualid_of_string "Coq.Init.Datatypes.bool"))))
  | MLPASome p -> 
    MLPConstr (ident_of_string "Some", [transform_pat_constrs p]), ty
  | MLPANone -> MLPConstr (ident_of_string "None", []), ty
  | _ -> lpat, ty
and transform_pat_constrs_list lpat_list =
  List.map transform_pat_constrs lpat_list

(* Transform added constrs (the ones with an A) to basic constrs. *)
let rec transform_constrs (lterm, ty) = match lterm with
  | MLTTuple tl -> MLTTuple (transform_constrs_list tl), ty
  | MLTRecord (il, tl) -> MLTRecord (il, transform_constrs_list tl), ty
  | MLTConstr (i, tl) -> MLTConstr (i, transform_constrs_list tl), ty
  | MLTFun (i, tl, m) -> MLTFun (i, transform_constrs_list tl, m), ty
  | MLTFunNot (i, tl, m) -> MLTFunNot (i, transform_constrs_list tl, m), ty
  | MLTMatch (t, an, ptl) -> MLTMatch (transform_constrs t, an,
    List.map (fun (p, t, an) -> 
      transform_pat_constrs p, transform_constrs t, an) ptl), ty
  | MLTATrue -> MLTConstr (ident_of_string "true", []), 
    (CTSum [ident_of_string "true";ident_of_string "false"], 
      Some (constr_of_global 
        (locate (qualid_of_string "Coq.Init.Datatypes.bool"))))
  | MLTAFalse -> MLTConstr (ident_of_string "false", []), 
    (CTSum [ident_of_string "true";ident_of_string "false"], 
      Some (constr_of_global
        (locate (qualid_of_string "Coq.Init.Datatypes.bool"))))
  | MLTASome t -> MLTConstr (ident_of_string "Some", [transform_constrs t]), ty
  | MLTANone -> MLTConstr (ident_of_string "None", []), ty
  | _ -> lterm, ty
and transform_constrs_list lterm_list =
  List.map transform_constrs lterm_list

(* We must add this constructors: true, false, Some, None *)
let add_standard_constr_to_spec env = 
  let true_cstr = constr_of_global
    (locate (qualid_of_string "Coq.Init.Datatypes.true"))
  and false_cstr = constr_of_global
    (locate (qualid_of_string "Coq.Init.Datatypes.false"))
  and some_cstr = constr_of_global
    (locate (qualid_of_string "Coq.Init.Datatypes.Some"))
  and none_cstr = constr_of_global
    (locate (qualid_of_string "Coq.Init.Datatypes.None"))
  in 
let henv = { env.extr_henv with cstrs =
    (ident_of_string "true", true_cstr)::(ident_of_string "false", false_cstr)::
    (ident_of_string "None", none_cstr)::(ident_of_string "Some", some_cstr)::
    env.extr_henv.cstrs } in
  { env with extr_henv = henv }

(* Change the type of incomplete function with the option type. *)
let rec complete_fun_with_option env f = 
  let rec cfwo_rec (lterm, ty) = match lterm with
    | MLTVar _ | MLTTuple _ | MLTRecord _ | MLTConstr _ | MLTConst _ | MLTFun _ 
    | MLTFunNot _ | MLTATrue | MLTAFalse | MLTASome _ | MLTANone -> 
      if fix_get_completion_status env f.mlfun_name then
        let opt = constr_of_global 
          (locate (qualid_of_string "Coq.Init.Datatypes.option")) in
        match ty with
        | _, Some ctyp ->
          let ctyp = Some (mkApp (opt, [|ctyp|])) in
          let typ = (CTSum [ident_of_string "Some";ident_of_string "None"], 
            ctyp) in
          MLTASome (lterm, ty), typ
        | _ -> assert false
      else lterm, ty
    | MLTMatch ((MLTFun(i,args,m), (_,Some ctyp)), an, ptl) 
    when fix_get_completion_status env i -> 

     let opt = constr_of_global 
       (locate (qualid_of_string "Coq.Init.Datatypes.option")) in
     let ctyp = Some (mkApp (opt, [|ctyp|])) in
     let typ = (CTSum [ident_of_string "Some";ident_of_string "None"], ctyp) in
     MLTMatch ((MLTFun(i,args,m), typ), an,
       List.map (fun (p, t, an) -> match p with
         | MLPWild, _ -> p, cfwo_rec t, an
         | _ -> (MLPASome p, typ), cfwo_rec t, an) ptl), ty
    | MLTMatch (lt, an, ptl) -> MLTMatch (lt, an,
       List.map (fun (p, t, an) -> p, cfwo_rec t, an) ptl), ty
    | MLTALin _ -> lterm, ty
    | MLTADefault -> lterm, ty in
  {f with mlfun_body = cfwo_rec f.mlfun_body}

(* Generates a Coq natural number. *)
let rec gen_coq_nat n = if n = 0 then 
    constr_of_global (locate (qualid_of_string "Coq.Init.Datatypes.O"))
  else
    let s = constr_of_global 
      (locate (qualid_of_string "Coq.Init.Datatypes.S")) in
    mkApp (s, [|gen_coq_nat (n-1)|])

(* Add a counter for FixCount recursion style in an ml function. *)
(* The ml function must already have been completed with option type
   prior to use this function. *)
let add_ml_counter env f = 
  let fname = f.mlfun_name in
  let (mlt, typ) = f.mlfun_body in
  let coq_nat = Some (constr_of_global 
      (locate (qualid_of_string "Coq.Init.Datatypes.nat"))) in
  let nat_typ = CTSum [ident_of_string "O"; ident_of_string "S"], coq_nat in
  let fcount = MLTVar (ident_of_string "fcounter"), nat_typ in
  let fcount_pat = MLPVar (ident_of_string "fcounter"), nat_typ in
  let rec adapt_func_calls (mlt, typ) = match mlt with
    | MLTTuple tl -> MLTTuple (List.map adapt_func_calls tl), typ
    | MLTRecord (il, tl) -> MLTRecord (il, List.map adapt_func_calls tl), typ
    | MLTConstr (i, tl) -> MLTConstr (i, List.map adapt_func_calls tl), typ
    | MLTFun (i, tl, mo) -> begin match fix_get_recursion_style env i with
        | FixCount -> MLTFun (i, fcount::tl, mo), typ         
        | _ -> mlt, typ
      end
    | MLTFunNot (i, tl, mo) -> begin match fix_get_recursion_style env i with
        | FixCount -> MLTFunNot (i, fcount::tl, mo), typ         
        | _ -> mlt, typ
      end
    | MLTMatch (mt, an, ptal) -> let mt' = adapt_func_calls mt in
      let ptal' = List.map (fun (p, t, a) -> (p, adapt_func_calls t, a)) ptal in
      MLTMatch (mt', an, ptal'), typ
    | MLTASome t -> MLTASome (adapt_func_calls t), typ
    | _ -> mlt, typ in
  let mlt', args' = match fix_get_recursion_style env fname with 
    | FixCount -> let ptal = [
        ((MLPConstr (ident_of_string "O", []), nat_typ), 
                (MLTConstr (ident_of_string "None", []), typ), []);
        ((MLPConstr (ident_of_string "S", [fcount_pat]), nat_typ), 
                (adapt_func_calls (mlt, typ)), [])
      ] in
      (MLTMatch (fcount, [], ptal), typ), 
        (ident_of_string "fcounter")::f.mlfun_args
    | _ -> adapt_func_calls (mlt, typ), f.mlfun_args in
  { mlfun_name = fname;
    mlfun_body = mlt';
    mlfun_args = args' }


(* Generates a fix function from a ml function. *)
let build_fix_fun (env, id_fun) f =
  let build_f comp f =
    let mlt = transform_constrs f.mlfun_body in
    let fterm = build_fix_term comp (env, id_fun) [] mlt in
    { fixfun_name = f.mlfun_name;
      fixfun_args = f.mlfun_args;
      fixfun_body = fterm; } in
  let f = complete_fun_with_option env f in
  let f = add_ml_counter env f in
  build_f (fix_get_completion_status env f.mlfun_name) f

(* Generates one fix function. *)
let gen_fix_fun env id =
  let f = extr_get_mlfun env id in
  build_fix_fun (env, id) f

(* TODO: support for already extracted functions. *)
(* Builds the fix env. After calling this function, we still have to check
   for dependencies. *)
let build_initial_fix_env env = 
  (* Fake env to avoid the Not_found exception while generating fix funs *)
  let fake_fix_env = List.map (fun (spec_id, _) -> 
      (spec_id, (extr_get_mlfun env spec_id).mlfun_name),
      (false, StructRec 0)
    ) env.extr_mlfuns in
  let env = {env with extr_fix_env = fake_fix_env} in
  let spec_ids = List.map fst env.extr_mlfuns in
  List.fold_left (fun fix_env spec_id -> 
    let fn = (extr_get_mlfun env spec_id).mlfun_name in
    let rs = match get_user_recursion_style env spec_id with
      | Some rs -> rs
      | None -> StructRec 1 in
    let compl = match rs with
      | FixCount -> true
      | _ -> begin try let _ = gen_fix_fun env spec_id in false 
             with RelExtImcompleteFunction -> true end in
    ((spec_id, fn), (compl, rs))::fix_env
  ) [] spec_ids

let rec list_exists_tuple f l = match l with
  | [] -> (false, false)
  | t::tail -> let (a, b) = f t in
    let (a', b') = list_exists_tuple f tail in
    (a || a', b || b')

let propag_one_func env (spec_id, mlf) = 
  let rec browse_func (mlt, _) = match mlt with
    | MLTTuple tl -> list_exists_tuple browse_func tl
    | MLTRecord (il, tl) -> list_exists_tuple browse_func tl
    | MLTConstr (i, tl) -> list_exists_tuple browse_func tl
    | MLTFun (i, _, _) | MLTFunNot (i, _, _) -> 
      let dep_compl = fix_get_completion_status env i in
      let dep_count = match fix_get_recursion_style env i with
        | FixCount -> true
        | _ -> false in
      (dep_compl, dep_count)
    | MLTMatch (mt, _, ptal) -> 
      let tl = mt::(List.map (fun (_, t, _) -> t) ptal) in
      list_exists_tuple browse_func tl
    | _ -> (false, false) in
  let fn = mlf.mlfun_name in
  let dep_compl, dep_count = browse_func mlf.mlfun_body in
  let compl = fix_get_completion_status env fn in
  let full = is_full_extraction (List.hd (extr_get_modes env spec_id)) in
  let env = if full then
    fix_set_completion_status env fn (dep_compl || compl) 
  else env in
  if dep_count then
    let env = fix_set_recursion_style env fn FixCount in
    fix_set_completion_status env fn true
  else env

let build_fix_env env =
  let rec build_until_the_end env =
    let nenv = List.fold_left propag_one_func env env.extr_mlfuns in
    if nenv.extr_fix_env = env.extr_fix_env then env
    else build_until_the_end nenv in
  build_until_the_end {env with extr_fix_env = build_initial_fix_env env}

let mk_pa_var fn sn = {
  pi_func_name = fn;
  pi_spec_name = sn;
}

let rec list_exists_assoc f l = match l with
  | [] -> false, None
  | e::t -> let b, r = f e in if b then true, r else list_exists_assoc f t

let mk_po pm_n_opt = match pm_n_opt with
  | None -> assert false (* TODO: error message ? *)
  | Some pm_n -> { po_prem_name = string_of_ident pm_n }

let build_proof_scheme fixfun = 
  let rec rec_ps (ft, (ty, cty)) an = match ft with
    | FixCase (t, anmatch, iltl) -> let cstr_list = match t with
        | (_, (CTSum cl, _)) -> List.map string_of_ident cl
        | _ -> anomalylabstrm "RelationExtraction" 
                 (str "Missing type information") in
      List.flatten (List.map2 (fun (il, next_t, anpat) cstr ->
        let pall = rec_ps next_t anpat in
        List.map (fun (p, al) -> let b, pm_n = list_exists_assoc (fun a -> 
          match p with
            | Some pn -> a.pa_prop_name = pn, Some a.pa_prem_name
            | None -> false, None) anmatch in
        if b then
          p, (CaseConstr (t, cstr, List.map 
            (fun i -> mk_pa_var (string_of_ident i) None) il, mk_po pm_n), None)::al
        else p, (CaseDum (t, cstr, List.map 
               (fun i -> mk_pa_var (string_of_ident i) None) il), None)::al) pall
      ) iltl cstr_list)
    | FixLetin (i, t, next_t, anlet) -> let pall = rec_ps next_t an in
      List.map (fun (p, al) -> let b, pm_n = list_exists_assoc (fun a -> 
        match p with
          | Some pn -> a.pa_prop_name = pn, Some a.pa_prem_name
          | None -> false, None) anlet in
        if b then
        p, (LetVar (mk_pa_var (string_of_ident i) None, t, mk_po pm_n), None)::al
      else p, (LetDum (mk_pa_var (string_of_ident i) None, t), None)::al) pall
    | _ -> begin match an with 
      | [] -> [None, [OutputTerm None, None]]
      | ({pa_prop_name = pn; pa_renamings = _})::_ -> 
        (* a list with more than one element can occur in relaxed extraction *)
        [Some pn, [OutputTerm (Some (ft, (ty, cty))), None]]
      | _ -> assert false
    end in
  let pall = rec_ps fixfun.fixfun_body [] in
  let branches = List.map (fun (p, al) -> let p = match p with
      | None -> None
      | Some p -> Some (string_of_ident p) in
    {psb_prop_name = p; psb_branch = al}) pall in
  { scheme_branches = branches; }

(* Build all fix functions. *)
let build_all_fixfuns env =
  let env = add_standard_constr_to_spec env in
  let env = build_fix_env env in
  let ids = List.map fst env.extr_mlfuns in
  List.fold_left (fun env id -> 
    let fixfun = gen_fix_fun env id in
    { env with extr_fixfuns = (id, 
      (fixfun, build_proof_scheme fixfun))::env.extr_fixfuns }
  ) env ids
  
