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

open Host_stuff
open Proof_scheme

exception RelationExtractionError of string

(*********)
(* Utils *)
(*********)

let rec concat_list l sep = match l with
  | [] -> ""
  | [a] -> a
  | a::tl -> a ^ sep ^ (concat_list tl sep)

let flatmap f l = List.flatten ((List.map f) l)


(***************)
(* Identifiers *)
(***************)

type ident = string
let string_of_ident i = i
let ident_of_string i = i
let fresh_string_id =
  let i = ref 0 in
  fun base_name () -> i := !i + 1; base_name ^ (string_of_int !i)
let fresh_ident base_name () = ident_of_string (fresh_string_id base_name ())


(*************************)
(* Annotation for proofs *)
(*************************)

type annot_atom = {
  pa_prop_name : ident;
  pa_prem_name : ident;
  pa_renamings : (ident * ident) list;
}

type pannot = annot_atom list

let pp_pannot an = "{" ^ concat_list 
  (List.map (fun a -> string_of_ident a.pa_prop_name ^ "(" ^ 
   string_of_ident a.pa_prem_name ^ ")") an) "&" ^ "}"

let option_name_to_ident opt_name = match opt_name with
  | None -> ident_of_string ""
  | Some id -> id

let mk_an prop_name prem_name = 
  [{ pa_prop_name = option_name_to_ident prop_name; 
     pa_prem_name = option_name_to_ident prem_name; 
     pa_renamings = [] }]

let an_add_prop an prop_name prem_name = (mk_an prop_name prem_name)@an

(* TODO: add variables renamings in annotations *)


(*********)
(* Types *)
(*********)

type clear_type = 
  | CTTuple of clear_type list
  | CTSum of ident list
  | CTNone
type 'htyp term_type = (clear_type * 'htyp host_term_type)
type ('t, 'htyp) typed = ('t * 'htyp term_type)

let rec pp_clear_type t = match t with
  | CTTuple ctl -> "(" ^ concat_list (List.map pp_clear_type ctl) ", " ^ ")"
  | CTSum il -> concat_list (List.map string_of_ident il) "|"
  | CTNone -> "%notype%"

let pp_term_type (ct, _) = pp_clear_type ct


(************)
(* ML Terms *)
(************)

type 'htyp untyped_ml_pat =
  | MLPVar of ident
  | MLPTuple of 'htyp ml_pat list
  | MLPRecord of ident list * 'htyp ml_pat list
  | MLPConstr of ident * 'htyp ml_pat list
  | MLPConst of ident
  | MLPWild
  | MLPATrue | MLPAFalse
  | MLPASome of 'htyp ml_pat | MLPANone
and 'htyp ml_pat = ('htyp untyped_ml_pat, 'htyp) typed

type mode_option = 
  | MInput
  | MOutput
  | MSkip
type mode = mode_option list

let string_of_mode mode = 
  if List.for_all (fun mo -> mo != MOutput) mode then "_full"
  else let rec rec_som mode i =  match mode with
    | [] -> ""
    | MInput::tl_mode -> (string_of_int i) ^ (rec_som tl_mode (i+1))
    | MOutput::tl_mode -> rec_som tl_mode (i+1)
    | MSkip::tl_mode -> rec_som tl_mode i in
  rec_som mode 1

let string_of_mode_full mode = 
  let rec rec_som mode i =  match mode with
    | [] -> ""
    | MInput::tl_mode -> (string_of_int i) ^ (rec_som tl_mode (i+1))
    | MOutput::tl_mode -> rec_som tl_mode (i+1)
    | MSkip::tl_mode -> rec_som tl_mode i in
  rec_som mode 1

type 'htyp untyped_ml_term =
  | MLTVar of ident
  | MLTTuple of 'htyp ml_term list
  | MLTRecord of ident list * 'htyp ml_term list
  | MLTConstr of ident * 'htyp ml_term list
  | MLTConst of ident
  | MLTFun of ident * 'htyp ml_term list * mode option
  | MLTFunNot of ident * 'htyp ml_term list * mode option
  | MLTMatch of 'htyp ml_term * pannot * 
    ('htyp ml_pat * 'htyp ml_term * pannot) list
  | MLTALin of ('htyp ml_term * 'htyp ml_term) list
  | MLTATrue | MLTAFalse
  | MLTASome of 'htyp ml_term | MLTANone
  | MLTADefault
and 'htyp ml_term = ('htyp untyped_ml_term, 'htyp) typed

let rec concat_list l sep = match l with
  | [] -> ""
  | [a] -> a
  | a::tl -> a ^ sep ^ (concat_list tl sep)

let rec pp_untyped_ml_pat pat = match pat with
  | MLPVar i -> string_of_ident i
  | MLPTuple pl -> "(" ^ (concat_list (List.map pp_ml_pat pl) ", ") ^ ")"
  | MLPRecord (il, pl) -> "{" ^ 
      (concat_list (List.map2 (fun i t -> string_of_ident i ^ " = " ^
        (pp_ml_pat t)) il pl) "; ") ^ "}"
  | MLPConstr (i, []) -> string_of_ident i
  | MLPConstr (i, pl) -> 
     string_of_ident i ^ " (" ^ (concat_list (List.map pp_ml_pat pl) ", ") ^ ")"
  | MLPConst i -> i
  | MLPWild -> "_"
  | MLPATrue -> "true"
  | MLPAFalse -> "false"
  | MLPANone -> "None" 
  | MLPASome p -> "Some (" ^ (pp_ml_pat p) ^ ")"
and pp_ml_pat (pat, ty) = pp_untyped_ml_pat pat ^ match ty with (CTSum _, _) -> "*" | _ -> ""

let rec pp_ml_untyped_term inc term = match term with
  | MLTVar i -> "@" ^ string_of_ident i
  | MLTTuple tl -> 
        "(" ^ (concat_list (List.map (pp_ml_term_aux inc) tl) ", ") ^ ")"
  | MLTRecord (il, tl) -> "{" ^ (concat_list 
      (List.map2 (fun i t -> string_of_ident i ^ " = " ^
        (pp_ml_term_aux inc t)) il tl) "; ") ^ "}"
  | MLTConstr (i, []) -> string_of_ident i
  | MLTConstr (i, tl) -> string_of_ident i ^ 
        "(" ^ (concat_list (List.map (pp_ml_term_aux inc) tl) ", ") ^ ")"
  | MLTConst i -> string_of_ident i
  | MLTFun (i, tl, Some m) -> string_of_ident i ^ string_of_mode m ^ " " ^
    (concat_list (List.map (fun t -> "(" ^ pp_ml_term_aux inc t ^ ")") tl) " ")
  | MLTFun (i, tl, _) -> string_of_ident i ^ " " ^
    (concat_list (List.map (fun t -> "(" ^ pp_ml_term_aux inc t ^ ")") tl) " ")
  | MLTFunNot (i, tl, _) -> "~ (" ^ 
    pp_ml_untyped_term inc (MLTFun (i, tl, None)) ^ ")"
  | MLTMatch (t, an, ptl) -> pp_pannot an ^ "begin match " ^ 
      (pp_ml_term_aux inc t) ^ " with\n" ^
      concat_list (List.map (pp_ml_pattern (inc ^ "  ")) ptl) "" ^ " end"
  | MLTALin vvl -> concat_list (List.map (fun (v1, v2) -> 
          pp_ml_term_aux inc v1 ^ " = " ^ pp_ml_term_aux inc v2) vvl) " && "
  | MLTATrue -> "true" 
  | MLTAFalse -> "false" 
  | MLTANone -> "None" 
  | MLTASome t -> "Some (" ^ (pp_ml_term_aux inc t) ^ ")"
  | MLTADefault -> "default_case"
and pp_ml_term_aux inc (t, ty) = pp_ml_untyped_term inc t ^ 
  match ty with (CTSum _, _) -> "*" | _ -> ""
and pp_ml_pattern inc (pat, term, an) = 
  inc ^ pp_pannot an ^ "| " ^ (pp_ml_pat pat) ^ " -> " ^ 
  (pp_ml_term_aux inc term) ^ "\n"
let pp_ml_term t = pp_ml_term_aux "" t


(******************)
(* Specifications *)
(******************)

type 'htyp premisse =
  | PMTerm of 'htyp ml_term * ident option
  | PMNot of 'htyp premisse * ident option
  | PMOr of 'htyp premisse list * ident option
  | PMAnd of 'htyp premisse list * ident option
  | PMChoice of 'htyp premisse list * ident option

type 'htyp property = {
  prop_name : ident option;
  prop_vars : ident list;
  prop_prems : 'htyp premisse list;
  prop_concl : 'htyp ml_term;
}

type 'htyp spec = {
  spec_name : ident;
  spec_args_types : 'htyp term_type list;
  spec_props : 'htyp property list;
} 

let rec pp_premisse prem = match prem with
  | PMTerm (t, _) -> pp_ml_term t
  | PMNot (pm, _) -> "not " ^ pp_premisse pm
  | PMOr (pml, _) -> "(" ^ concat_list (List.map pp_premisse pml) " || " ^ ")"
  | PMAnd (pml, _) -> "(" ^ concat_list (List.map pp_premisse pml) " && " ^ ")"
  | PMChoice (pml, _) -> "(" ^ concat_list (List.map pp_premisse pml) " | " ^ ")"

let pp_property prop = begin match prop.prop_name with
    | None -> ""
    | Some i -> string_of_ident i ^ ": " end ^ 
  begin match prop.prop_vars with 
    | [] -> ""
    | _ -> "\\-∕ " ^ concat_list (List.map string_of_ident prop.prop_vars) " " ^ 
      ": " end ^
  begin match prop.prop_prems with
    | [] -> ""
    | _ -> concat_list (List.map pp_premisse prop.prop_prems) " -> " ^ 
      " -> " end ^
  pp_ml_term prop.prop_concl

let pp_spec spec = "Specification " ^ string_of_ident spec.spec_name ^ ": " ^
  concat_list (List.map pp_term_type spec.spec_args_types) " -> " ^ " :=\n" ^
  concat_list (List.map pp_property spec.spec_props) "\n"


(****************)
(* ML functions *)
(****************)

type 'htyp ml_fun = {
  mlfun_name : ident;
  mlfun_args : ident list;
  mlfun_body : 'htyp ml_term;
}

let pp_ml_fun f =
  "let rec " ^ string_of_ident f.mlfun_name ^ " " ^
  concat_list (List.map string_of_ident f.mlfun_args) " " ^ " =\n" ^
  pp_ml_term f.mlfun_body


(*********)
(* Trees *)
(*********)

(* Tree node content *)
type 'htyp node_type =
  | NTPrem of 'htyp ml_term
  | NTConcl of 'htyp ml_term

(* Tree structure *)
type 'htyp tree_node =
  | TreeNode of ('htyp node_type * 'htyp tree_node list * pannot)
  | TreeOutput of ('htyp node_type * 'htyp ml_term * pannot) 
                               (* ml_term is a conclusion *)

type 'htyp tree = 'htyp tree_node list

let pp_node_type nt = match nt with
  | NTPrem mlt -> pp_ml_term mlt
  | NTConcl mlt -> "[" ^ pp_ml_term mlt ^ "]"

let rec pp_tree_node inc tn = match tn with
  | TreeNode (nt, tnl, _) -> inc ^ (pp_node_type nt) ^ "\n" ^
    (concat_list (List.map (pp_tree_node (inc^"  ")) tnl) "\n")
  | TreeOutput (nt, mlt, _) -> inc ^ (pp_node_type nt) ^ " -> " ^
    pp_ml_term mlt

let pp_tree tree = concat_list (List.map (pp_tree_node "") tree) "\n"


(*****************)
(* Fix functions *)
(*****************)

type 'htyp fix_untyped_term =
  | FixVar of ident
(*  | FixRecord of ident list * fix_term list*)
  | FixConstr of ident * 'htyp fix_term list
  | FixConst of ident
  | FixFun of ident * 'htyp fix_term list
  | FixFunNot of ident * 'htyp fix_term list
  | FixCase of 'htyp fix_term * pannot * 
      (ident list * 'htyp fix_term * pannot) list
  | FixLetin of ident * 'htyp fix_term * 'htyp fix_term * pannot
  | FixSome of 'htyp fix_term
  | FixNone
  | FixTrue 
  | FixFalse 
and 'htyp fix_term = ('htyp fix_untyped_term, 'htyp) typed

type 'htyp fix_fun = {
  fixfun_name : ident;
  fixfun_args : ident list;
  fixfun_body : 'htyp fix_term;
}

let rec pp_fix_untyped_term inc t = match t with
  | FixVar i -> string_of_ident i
  | FixConstr (i, []) -> string_of_ident i
  | FixConstr (i, tl) -> string_of_ident i ^ 
        "(" ^ (concat_list (List.map (pp_fix_term_aux inc) tl) ", ") ^ ")"
  | FixConst i -> string_of_ident i
  | FixFun (i, tl) -> string_of_ident i ^ " " ^
    (concat_list (List.map (fun t -> "(" ^ pp_fix_term_aux inc t ^ ")") tl) " ")
  | FixFunNot (i, tl) -> 
            "not (" ^ pp_fix_untyped_term inc (FixFun (i, tl)) ^ ")"
  | FixCase (t, an, iltl) -> let inc' = inc ^ "  " in
    pp_pannot an ^ "Case " ^ (pp_fix_term_aux inc t) ^ "\n" ^ concat_list
    (List.map (fun (il, t, an) -> inc' ^ pp_pannot an ^ "| " ^
      concat_list (List.map string_of_ident il) " " ^ " -> " ^ 
      pp_fix_term_aux inc' t) iltl) "\n"
  | FixSome t -> "Some " ^ pp_fix_term_aux inc t
  | FixNone -> "None"
  | FixTrue -> "True"
  | FixFalse -> "False"
  | FixLetin (i, l, t, an) -> pp_pannot an ^ "let " ^ 
    string_of_ident i ^ " = " ^ 
    pp_fix_term_aux inc l ^ " in " ^ pp_fix_term_aux inc t
and pp_fix_term_aux inc (t, ty) = pp_fix_untyped_term inc t ^ "{" ^ 
                                 (pp_term_type ty) ^ "}"
and pp_fix_term t = pp_fix_term_aux "" t

let pp_fix_fun fixfun =
  "FixPred " ^ string_of_ident fixfun.fixfun_name ^ " " ^ 
  concat_list (List.map string_of_ident fixfun.fixfun_args) " " ^ " =\n" ^
  pp_fix_term fixfun.fixfun_body


(**************)
(* Extraction *)
(**************)

type recursion_style =
  | StructRec of int
  | FixCount

type ('htyp, 'henv) extract_env = {
  extr_modes : (ident * mode list) list;
  extr_extractions : (ident * (ident option * bool * recursion_style option)) list;
  extr_specs : (ident * 'htyp spec) list;
  extr_trees : (ident * 'htyp tree) list;
  extr_mlfuns : (ident * 'htyp ml_fun) list;
  extr_fixfuns : (ident * ('htyp fix_fun * ('htyp fix_term) proof_scheme)) list;
  extr_henv : 'henv host_env;
  extr_hf : ('htyp, 'henv) host_functions;
  extr_fix_env : ((ident * ident) * (bool * recursion_style)) list;
}

let extr_get_modes env i =
  try List.assoc i env.extr_modes with Not_found -> []

let extr_get_spec env i = List.assoc i env.extr_specs
let extr_get_spec_ord env i = 
  let (_, ord, _) =  List.assoc i env.extr_extractions in
  ord
let extr_get_tree env i = List.assoc i env.extr_trees
let extr_get_mlfun env i = List.assoc i env.extr_mlfuns
let extr_get_fixfun env i = List.assoc i env.extr_fixfuns

let rec fix_assoc fix_env id = match fix_env with
  | [] -> raise Not_found
  | ((i1, i2), v)::_ when i1 = id || i2 = id -> v
  | _::tail -> fix_assoc tail id

let rec fix_set fix_env id v = match fix_env with
  | [] -> raise Not_found
  | ((i1, i2), v')::tail when i1 = id || i2 = id -> ((i1, i2), v)::tail
  | x::tail -> x::(fix_set tail id v)

let fix_get_completion_status env id =
  let (cs, _) = fix_assoc env.extr_fix_env id in cs

let fix_get_recursion_style env id =
  let (_, rs) = fix_assoc env.extr_fix_env id in rs

let fix_set_completion_status env id cs =
  let (_, rs) = fix_assoc env.extr_fix_env id in 
  {env with extr_fix_env = fix_set env.extr_fix_env id (cs, rs)}

let fix_set_recursion_style env id rs =
  let (cs, _) = fix_assoc env.extr_fix_env id in 
  {env with extr_fix_env = fix_set env.extr_fix_env id (cs, rs)}

let get_spec_id_from_fname env fn = 
  let rec find_id mlf_list = match mlf_list with
    | [] -> raise Not_found
    | (id, mlf)::_ when mlf.mlfun_name = fn -> id
    | _::mlf_tail -> find_id mlf_tail in
  find_id env.extr_mlfuns

let get_user_recursion_style env id =
  try let (_, _, rs) = List.assoc id env.extr_extractions in rs
  with Not_found -> try let (_, _, rs) = 
    List.assoc (get_spec_id_from_fname env id) env.extr_extractions in rs
  with Not_found -> None

let is_rec_style_count env id = match fix_get_recursion_style env id with
  | FixCount -> true
  | _ -> false

let pp_extract_env env =
  "(********* Modes *********)\n\n" ^
  concat_list (List.map (fun (i, ml) -> 
    string_of_ident i ^ ": " ^
    concat_list (List.map string_of_mode_full ml) "; "
  ) env.extr_modes) "\n" ^
  "\n\n\n" ^
  "(********* Secifications *********)\n\n" ^
  concat_list (List.map pp_spec (List.map snd env.extr_specs)) "\n\n" ^ 
  "\n\n\n" ^
  "(********* Extracted functions *********)\n\n" ^
  concat_list (List.map pp_ml_fun (List.map snd env.extr_mlfuns)) "\n\n" 
  
let unknown_type env = CTNone, env.extr_hf.h_get_fake_type ()
let fake_type env t = t, unknown_type env

exception RelationExtractionProp of ident option * string

(************************)
(* Extraction algorithm *)
(************************)

(* Select inputs or outputs of a inductive predicate term *)
let get_in_terms_func env mlt =
  let rec get_rec args mode = match (args, mode) with
    | (a::tl_args, MInput::tl_mode) -> a::(get_rec tl_args tl_mode)
    | (_::tl_args, MOutput::tl_mode) -> get_rec tl_args tl_mode
    | (_, MSkip::tl_mode) -> get_rec args tl_mode
    | _ -> [] in
  match mlt with
    | MLTFun (_, _, None), _ | MLTFunNot (_, _, None), _ ->
      [mlt]
    | MLTFun (_, args, Some m), _ | MLTFunNot (_, args, Some m), _ ->
      get_rec args m
    | _ -> assert false
let get_out_terms_func env mlt =
  let rec get_rec args mode = match (args, mode) with
    | (a::tl_args, MOutput::tl_mode) -> a::(get_rec tl_args tl_mode)
    | (_::tl_args, MInput::tl_mode) -> get_rec tl_args tl_mode
    | (_, MSkip::tl_mode) -> get_rec args tl_mode
    | _ -> [] in
  match mlt with
    | MLTFun (_, _, None), _ -> [fake_type env MLTATrue]
    | MLTFunNot (_, _, None), _ -> [fake_type env MLTAFalse]
    | MLTFun (_, args, Some m), _ ->
      let outputs = get_rec args m in 
      if outputs = [] then [fake_type env MLTATrue] else outputs
    | MLTFunNot (_, args, Some m), _ ->
      let outputs = get_rec args m in 
      if outputs = [] then [fake_type env MLTAFalse] else outputs
    | _ -> assert false

(* Get a list of variables in a term *)
let rec get_variables (t, _) = match t with
  | MLTATrue | MLTAFalse -> []
  | MLTConst _ -> []
  | MLTVar i -> [i]
  | MLTTuple tl | MLTRecord (_, tl) | MLTConstr (_, tl)
  | MLTFun (_, tl, _) | MLTFunNot (_, tl, _) ->
    List.flatten (List.map get_variables tl)
  | _ -> assert false

(* Select inputs or outputs of a node_type element *)
(* for these 4 functions, in and out are reversed for conclusion nodes *)
let get_in_terms env nt = match nt with
  | NTPrem mlt -> get_in_terms_func env mlt
  | NTConcl mlt -> get_out_terms_func env mlt
let get_out_terms env nt = match nt with
  | NTPrem mlt -> get_out_terms_func env mlt
  | NTConcl mlt -> get_in_terms_func env mlt
(* Get variables in inputs or outputs of a node_type element *)
let get_in_vars env nt = 
  List.flatten (List.map get_variables (get_in_terms env nt))
let get_out_vars env nt = 
  List.flatten (List.map get_variables (get_out_terms env nt))

(* Variable substitution in a term *)
let rename_var i mapping = if List.mem_assoc i mapping then
  List.assoc i mapping else i

(* Find a variables substitution in order to make term and ref_term equals *)
let rec find_renaming_terms mapping (term,_) (ref_term,_) = 
match term, ref_term with
  | (MLTConst i1, MLTConst i2) when i1 = i2 -> mapping
  | (MLTVar i1, MLTVar i2) -> 
(* TODO: verify that 2 variables are not renamed to the same variable. *)
      if (rename_var i1 mapping) = i2 then mapping else 
      if List.mem_assoc i1 mapping then failwith "impossible"
      else (i1, i2)::mapping
  | (MLTTuple tl1, MLTTuple tl2) | (MLTRecord (_, tl1), MLTRecord (_, tl2)) ->
    List.fold_left2 find_renaming_terms mapping tl1 tl2
  | (MLTConstr (i1, tl1), MLTConstr (i2, tl2)) when i1 = i2 ->
    List.fold_left2 find_renaming_terms mapping tl1 tl2
  | (MLTFun (_, tl1, _) | MLTFunNot (_, tl1, _)),
    (MLTFun (_, tl2, _) | MLTFunNot (_, tl2, _)) ->
    List.fold_left2 find_renaming_terms mapping tl1 tl2
  | _ -> failwith "impossible"

(* Find a variables substitution in order to make term_list and ref_term_list
   equals *)
let find_renaming term_list ref_term_list =
  List.fold_left2 find_renaming_terms [] term_list ref_term_list

(* Apply variables subsitution defined by mapping to the term *)
let rec rename_term mapping term = match term with
  | MLTConst _, _ -> term
  | MLTVar i, ty -> MLTVar (rename_var i mapping), ty
  | MLTTuple tl, ty -> MLTTuple (List.map (rename_term mapping) tl), ty
  | MLTRecord (il, tl), ty -> 
      MLTRecord (il, (List.map (rename_term mapping) tl)), ty
  | MLTConstr (i, tl), ty -> 
      MLTConstr (i, (List.map (rename_term mapping) tl)), ty
  | MLTFun (i, tl, m), ty -> 
      MLTFun (i, (List.map (rename_term mapping) tl), m), ty
  | MLTFunNot (i, tl, m), ty -> 
      MLTFunNot (i, (List.map (rename_term mapping) tl), m), ty
  | _ -> assert false

(* Apply variables subsitution defined by mapping to the node_type *)
let rename_nt mapping nt = match nt with
  | NTConcl t -> NTConcl (rename_term mapping t)
  | NTPrem t -> NTPrem (rename_term mapping t)

(* Apply variables subsitution defined by mapping to the property *)
let rename_prop mapping prop = 
  let rec rename_prem prem = match prem with
    | PMTerm (t, pn) -> PMTerm (rename_term mapping t, pn)
    | PMNot (pm, pn) -> PMNot (rename_prem pm, pn)
    | PMAnd (pml, pn) -> PMAnd (List.map rename_prem pml, pn)
    | PMOr (pml, pn) -> PMOr (List.map rename_prem pml, pn)
    | PMChoice (pml, pn) -> PMChoice (List.map rename_prem pml, pn)
  in
  { prop_name = prop.prop_name;
    prop_vars = prop.prop_vars;
    prop_prems = List.map rename_prem prop.prop_prems;
    prop_concl = rename_term mapping prop.prop_concl; }

(* try to rename a node_type and the associated property to fit a tree node *)
(* raises Failure "impossible" if it fails *)
(* after renaming nt can be inserted into tn *)
let rename_outputs_if_possible env nt tn prop = match nt, tn with
  | (NTConcl pdt, TreeNode (NTConcl refpdt, _, _)) -> 
    let ts, refts = get_in_terms_func env pdt, get_in_terms_func env refpdt in
    let mapping = find_renaming ts refts in
    (rename_nt mapping nt, rename_prop mapping prop)
  |          ( NTPrem ((MLTFun(i, _, m),_)as t),
    TreeNode ( (NTPrem ((MLTFun(ri, _, rm),_) as rt),_,_) )) 
                                                    when (i = ri && m = rm) ->
    let ts, refts = get_out_terms_func env t, get_out_terms_func env rt in
    let mapping = find_renaming ts refts in
    (rename_nt mapping nt, rename_prop mapping prop)
  | _ -> 
    failwith "impossible"

(* try to rename a node_type and the associated property to fit a tree node *)
(* raises Failure "impossible" if it fails *)
(* after renaming nt can be inserted in the tn list *)
let rename_inputs_if_possible env nt tn prop =  match nt, tn with
  | NTConcl _, _ -> (nt, prop) (* nothing to do *)
  |          ( NTPrem (((MLTFun(i,a,m)|MLTFunNot(i,a,m)),_) as t),
   TreeOutput ( (NTPrem (((MLTFun(ri,ra,rm)|MLTFunNot(ri,ra,rm)),_) as rt)),_,_) )
  |          ( NTPrem (((MLTFun(i,a,m)|MLTFunNot(i,a,m)),_) as t),
    TreeNode ( (NTPrem (((MLTFun(ri,ra,rm)|MLTFunNot(ri,ra,rm)),_) as rt),_,_) ))
                                                         when i=ri && m=rm ->
    let ts, refts = get_in_terms_func env t, get_in_terms_func env rt in
    let mapping = find_renaming ts refts in
(*maybe we can't rename inputs...*)
if List.length mapping > 0 then failwith "impossible"
else (nt, prop)
(*    (rename_nt mapping nt, rename_prop mapping prop) *)
  | _ ->  failwith "impossible"

  
(* Determinism check between terms *)
let rec test_det_terms (t1,_) (t2,_) = match (t1, t2) with
(* TODO: MLTFunNot can be used only with full mode or without mode (functions)*)
  | (MLTATrue, MLTAFalse) | (MLTAFalse, MLTATrue) -> true
  | (MLTTuple tl1, MLTTuple tl2) | (MLTRecord (_, tl1), MLTRecord (_, tl2)) ->
    List.exists2 test_det_terms tl1 tl2
  | (MLTConstr (i1, tl1) , MLTConstr (i2, tl2)) ->
    i1 <> i2 || (List.exists2 test_det_terms tl1 tl2)
  | (MLTConst i1, MLTConst i2) -> i1 <> i2
  | _ -> false

(* Determinism check between node_types *)
let test_det_nt env nt1 nt2 =
  List.exists2 test_det_terms (get_out_terms env nt1) (get_out_terms env nt2)

(* determinism test between nt and first nt of each tn *)
let test_det env nt tnl = List.for_all
  (fun tn -> let nt2 = (match tn with
    | TreeNode (nt, _, _) -> nt
    | TreeOutput (nt, _, _) -> nt 
                        ) in test_det_nt env nt nt2) tnl

(* Return true if t1 is an instance of t2, false else. *)
let terms_ordering env nt1 nt2 =
  let rec test_unif ((t1,_), (t2,_)) = match t1, t2 with
    | _, MLTVar _ -> true
    | MLTConst i1, MLTConst i2 -> i1 = i2
    | MLTConstr(i1, tl1), MLTConstr(i2, tl2) -> i1 = i2 &&
        List.for_all test_unif (List.combine tl1 tl2)
    | MLTRecord(_, tl1), MLTRecord(_, tl2) | MLTTuple tl1, MLTTuple tl2 ->
        List.for_all test_unif (List.combine tl1 tl2)
    | _ -> false in
  let rec test_inclusion ((t1,_), (t2,_)) = match t1, t2 with
    | MLTConst _, MLTVar _ -> true
    | MLTConstr _, MLTVar _ -> true
    | MLTConstr(_, tl1), MLTConstr(_, tl2)
    | MLTRecord(_, tl1), MLTRecord(_, tl2) | MLTTuple tl1, MLTTuple tl2 ->
        List.exists test_inclusion (List.combine tl1 tl2)
    | _ -> false in
  let terms1, terms2 = (get_out_terms env nt1), (get_out_terms env nt2) in
  let comb = List.combine terms1 terms2 in
  List.for_all test_unif comb && List.exists test_inclusion comb

(* Return
     true if nt1 is an instance of nt2 or if nt1 is not unifiable with nt2,
     false else. *)
let nt_partial_ordering env id_spec nt1 nt2 =
  let ord = extr_get_spec_ord env id_spec in
  test_det_nt env nt1 nt2 || (ord && (terms_ordering env nt1 nt2))

(* List inclusion *)
let rec included l1 l2 = match l1 with
  | [] -> true
  | a::t -> (List.mem a l2) && (included t l2)

(* Mode coherency analysis for a node_type *)
(* Check that all variables needed by nt are known *)
(* Don't chack anything for conclusion nodes, mca_check_output must be used
   for the output node *)
let mca_check env kv nt = match nt with
  | NTConcl _ -> true
  | NTPrem _ -> included (get_in_vars env nt) kv


(* Mode coherency analysis for a predicate term *)
(* Check that variables needed by the output are known *)
let mca_check_output env kv pdt = 
  let vars = get_in_vars env (NTConcl pdt) in
included vars kv

(* Get new knwon variables for the mode coherency analysis *)
(* Add variables calculated with nt to the known variables *)
let mca_add_vars env kv nt = (get_out_vars env nt) @ kv

(* Find all possible couple of the form (premisse, prop without the premisse) *)
let select_one_prem prop = 
  let rec select_rec prems = match prems with
    | [] -> []
    | p::ptail -> (p, ptail) ::
      (List.map (fun (p2, prems) -> (p2, p::prems)) (select_rec ptail)) in
  List.map (fun (p, prems) -> (p, {prop with prop_prems = prems}))
  (select_rec prop.prop_prems)
(* Quick version, but not exhaustive ! *)
let select_one_prem_quick prop = 
  match prop.prop_prems with
    | [] -> []
    | p::ptail -> [(p, {prop with prop_prems = ptail})]

(* try to rename inputs of a node type when this is necessary *)
let rename_inputs_if_needed env nt tnl prop = match tnl with
  | [] -> nt, prop
  | tn::_ -> rename_inputs_if_possible env nt tn prop

let rec remove_pm_not not_flag prem = match prem with
  | PMNot (pm, _) -> remove_pm_not (not not_flag) pm
  | PMTerm ((MLTFun (f, a, m), t), pn) -> 
    if not_flag then PMTerm ((MLTFunNot (f, a, m), t), pn)
    else prem
  | PMAnd (pms, pn) -> let pms' = List.map (remove_pm_not not_flag) pms in
    if not_flag then PMOr (pms', pn) else PMAnd (pms', pn)
  | PMOr (pms, pn) -> let pms' = List.map (remove_pm_not not_flag) pms in
    if not_flag then PMAnd (pms', pn) else PMOr (pms', pn)
  | PMChoice (pms, pn) -> PMChoice (List.map (remove_pm_not not_flag) pms, pn)
  | _ -> assert false

(* Put one premisse in conjunctive normal form *)
let rec develop_and and_prems = match and_prems with
  | [PMAnd (prems, _)] -> prems
  | (PMAnd (prems, _))::tl_and_prems ->
    let dev_prems = develop_and tl_and_prems in
    flatmap (fun p -> match p with PMOr (top_prems, _) ->
      List.map
       (fun dp -> match dp with 
         | PMOr (dtop_prems, _) -> PMOr (top_prems@dtop_prems, None)
         | _ -> assert false)
       dev_prems
      | _ -> assert false) prems
  | _ -> assert false
let normalize_and_or prem = let rec norm_rec prem = match prem with
  | PMTerm _ -> PMAnd ([PMOr ([prem], None)], None)
  | PMChoice _ -> PMAnd ([PMOr ([prem], None)], None)
  | PMAnd (prems, pm_n) -> PMAnd (flatmap
    (fun p -> match norm_rec p with PMAnd (ors, _) -> ors | _ -> assert false)
    prems, pm_n)
  | PMOr (prems, _) -> let nprems = List.map norm_rec prems in
    PMAnd (develop_and nprems, None) 
  | PMNot _ -> 
    assert false (* remove_pm_not must be applied before normalizing *) in
  let norm_prem = norm_rec (remove_pm_not false prem) in
  let simplify_or prem = match prem with
    | PMOr ([p], _) -> p
    | _ -> prem in
  match norm_prem with
    | PMAnd ([or_prem], _) -> simplify_or or_prem
    | PMAnd (or_prems, pm_n) -> PMAnd (List.map simplify_or or_prems, pm_n)
    | _ -> assert false


(* check if a node_type can be safely inserted in a treenode list *)
let check_insertable nt tnl = match tnl with
  | [] -> true
  | (TreeOutput(nt', _, _) | TreeNode(nt', _, _))::_ -> match (nt, nt') with
    | NTConcl ((MLTFun (f, _, m) | MLTFunNot (f, _, m)),_),
      NTConcl ((MLTFun (f', _, m') | MLTFunNot (f', _, m')),_)
    | NTPrem ((MLTFun (f, _, m) | MLTFunNot (f, _, m)),_),
      NTPrem ((MLTFun (f', _, m') | MLTFunNot (f', _, m')),_) ->
      f = f' && m = m'
    | _ -> false

(* insert the tree output (the last node) of a property *)
let rec insert_output env id_spec pm_n kv nt prop tnl = 
  if not (check_insertable nt tnl)
  then [] (* check logical terms compatibility *)
  else try let (nt, prop) = match tnl with (* rename inputs (matching term) *)
    | tn::_ -> rename_inputs_if_possible env nt tn prop
    | [] -> (nt, prop) in
  let tn = TreeOutput (nt, prop.prop_concl, mk_an prop.prop_name pm_n) in
  let rec io_rec tnl = match tnl with (* try to insert tn in the right place *)
    | [] -> [[TreeOutput (nt, prop.prop_concl, mk_an prop.prop_name pm_n)]]
      (* we can always insert at the end because 
                                        all the tests have been done before *)
    | ((TreeOutput (nti, _, _) | (TreeNode (nti, _, _))) as tni)::tntl ->
      if nt_partial_ordering env id_spec nti nt then 
                               (* nti still < nt, continue *)
        List.map (fun ntnl -> tni::ntnl) (io_rec tntl)
      else
        (* nt must be inserted *)
       let test_tail tni = match tni with
         | TreeNode (nti, _, _) | TreeOutput (nti, _, _) ->
            nt_partial_ordering env id_spec nt nti in
        if List.for_all test_tail tnl then [tn::tnl]
        else []
  in io_rec tnl
  with Failure "impossible" -> []

(* insert the last premisse of a property in a tree *)
let rec insert_last_prem_term env id_spec pm_n kv nt prop tnl = 
  insert_output env id_spec pm_n kv nt prop tnl

let rec insertion_recursor env id_spec prem_selector pm_n prop kv nt tnl = 
  let rec ir_rec tnl_acc = (* try to insert prop in every node or alone *)
    match tnl_acc with
      | [] -> (* no matching nt, insert alone *)
        let kv' = mca_add_vars env kv nt in
        List.map (fun nchild -> [TreeNode (nt, nchild, mk_an prop.prop_name pm_n)])
          (choose_prop_prem env id_spec prem_selector kv' prop [])
      | (TreeNode (nti, child, ani) as tni)::acc_tail -> 
        if nt_partial_ordering env id_spec nti nt then
          (* nti still < nt, continue *)
          List.map (fun tnl -> tni::tnl) (ir_rec acc_tail)
        else 
          let test_tail tn = match tn with
          | TreeNode (nti, _, _) | TreeOutput (nti, _, _) -> 
            nt_partial_ordering env id_spec nt nti in
        if List.for_all test_tail tnl_acc then
          (* nt can be inserted alone, before tni *)
          let kv' = mca_add_vars env kv nt in
          List.map ( fun nchild -> 
              (TreeNode (nt, nchild, mk_an prop.prop_name pm_n))::tnl_acc )
            (choose_prop_prem env id_spec prem_selector kv' prop [])
        else (* try to insert nt into tni *)
        ( try let rnt, rprop = rename_outputs_if_possible env nt tni prop in
          let kv' = mca_add_vars env kv rnt in
          List.map ( fun nchild -> 
              (TreeNode (nti, nchild, an_add_prop ani prop.prop_name pm_n))::
                acc_tail )
            (choose_prop_prem env id_spec prem_selector kv' rprop child)
         with Failure "impossible" -> [])
      | (TreeOutput(nti, _, _) as tni)::acc_tail -> 
        if nt_partial_ordering env id_spec nti nt then
          List.map (fun tnl -> tni::tnl) (ir_rec acc_tail)
        else []
(*      | tn::acc_tail -> if test_det nt [tn] then
          List.map (fun tnl -> tn::tnl) (ir_rec acc_tail)
        else []*)
  in ir_rec tnl

(* insert a premisse term in the treenode list *)
and insert_prem_term env id_spec prem_selector pm_n kv nt prop tnl =
  if not (check_insertable nt tnl) then []
  else 
  if mca_check env kv nt then
    try let nt, prop = rename_inputs_if_needed env nt tnl prop in
      insertion_recursor env id_spec prem_selector pm_n prop kv nt tnl
    with Failure "impossible" -> []
  else []

and not_full_mode m args =
  List.length (List.filter ((=) MInput) m) != List.length args

(* Insert prem into tnl. Select insert_last_prem_term or insert_prem_term *)
and insert_prem env id_spec prem_selector kv prem prop tnl = match prem with
  | PMTerm ((MLTFunNot (_, args, Some m), _), _) when not_full_mode m args -> []
  | PMTerm (pmt, pm_n) -> let nt = NTPrem pmt in
    if prop.prop_prems = [] then insert_last_prem_term env id_spec pm_n kv nt prop tnl
    else insert_prem_term env id_spec prem_selector pm_n kv nt prop tnl
  | PMAnd (pl, _) -> flatmap (fun prem ->
      let other_prems = List.filter (fun a -> a <> prem) pl in
      let nprop = { prop with prop_prems = other_prems@prop.prop_prems } in
      insert_prem env id_spec prem_selector kv prem nprop tnl
    ) pl
  | PMChoice (pl, _) -> flatmap
    (fun prem -> insert_prem env id_spec prem_selector kv prem prop tnl) pl
  | PMOr (pl, _) -> List.fold_left
    (fun trees prem -> flatmap
      (fun tnl -> insert_prem env id_spec prem_selector kv prem prop tnl) trees)
    [tnl] pl
  | PMNot _ -> assert false

(* Choose one premisse of prop to insert into tnl *)
and choose_prop_prem env id_spec prem_selector kv prop tnl =
  flatmap
    (fun (prem, prop) ->
      insert_prem env id_spec prem_selector kv (normalize_and_or prem) prop tnl)
    (prem_selector prop)
(* all trees that can result of the insertion of prop in tnl *)
let insert_prop_concl env id_spec prem_selector prop tnl =
  let nt = NTConcl prop.prop_concl in
  match prop.prop_prems with
    | [] -> (* insert the prop alone, as a tree output *)
      insert_output env id_spec None [] nt prop tnl
    | _ -> (* try to insert prop in one nt or alone *)
      insertion_recursor env id_spec prem_selector None prop [] nt tnl

(* TODO: optimization when there is no overlapping constructor to add after the
 * current one. It may be possible to test with nt_partial_ordering...
 *)
(* Build a tree from a specification *)
let tree_from_spec env prem_selector id_spec =
  let spec = extr_get_spec env id_spec in
  let trees = List.fold_left (fun tree_list prop -> 
    match tree_list with
    | [] -> begin match insert_prop_concl env id_spec prem_selector prop [] with
              | [] -> raise (RelationExtractionProp (prop.prop_name, ""))
              | l -> l
            end
    | _ -> begin match flatmap 
           (insert_prop_concl env id_spec prem_selector prop) tree_list with
        | [] -> raise (RelationExtractionProp (prop.prop_name, ""))
        | l -> l
      end
  ) [] spec.spec_props in
  match trees with
    | t::_ -> t
    | _ -> assert false

let tree_from_spec_with_quick_try env id_spec =
(*  try tree_from_spec env select_one_prem_quick id_spec
  with _ ->*)
    (* Quick algorithm failed. Trying the exhaustive one... *)
    tree_from_spec env select_one_prem id_spec

let make_trees env =
  let trees = List.map (fun (id_spec, _) -> 
      (id_spec, tree_from_spec_with_quick_try env id_spec))
    env.extr_extractions in
  {env with extr_trees = trees}

let get_pred_name env id_spec m =
  let name_from_mode m = ident_of_string
    (string_of_ident id_spec ^ (string_of_mode m)) in
  if not (List.mem_assoc id_spec env.extr_extractions) then
    name_from_mode m
  else match List.assoc id_spec env.extr_extractions with
    | Some fn, _, _ -> fn
    | None, _, _ -> name_from_mode m

let gen_args mode =
  let rec rec_args mode i = match mode with
    | [] -> []
    | MInput::m_tail -> ("p" ^ (string_of_int i)) :: (rec_args m_tail (i+1))
    | _::m_tail -> rec_args m_tail i in
  rec_args mode 1

let rec gen_term_pat (t, ty) = match t with
  | MLTVar i -> MLPVar i, ty
  | MLTTuple tl -> MLPTuple (List.map gen_term_pat tl), ty
  | MLTRecord (il, tl) -> MLPRecord (il, (List.map gen_term_pat tl)), ty
  | MLTConstr (i, tl) -> MLPConstr (i, (List.map gen_term_pat tl)), ty
  | MLTConst i -> MLPConst i, ty
  | MLTATrue -> MLPATrue, ty
  | MLTAFalse -> MLPAFalse, ty
  | _ -> failwith "TODO"

let gen_tuple env terms_list = match terms_list with
  | [t] -> t
  | _ -> fake_type env (MLTTuple terms_list)
let gen_tuple_pat env terms_list orig_nt = match terms_list with
  | [t] -> gen_term_pat t
  | _ -> fake_type env (MLPTuple (List.map gen_term_pat terms_list))


let rec lin_pat pat vars i lins = match pat with
  | MLPVar v, ty -> if included [v] vars then
    let nv = v ^ "_" ^ (string_of_int i) in
      ((MLPVar nv, ty), vars, i+1, ((MLTVar v, ty), (MLTVar nv, ty))::lins)
    else ((MLPVar v, ty), v::vars, i, lins)
  | MLPTuple pl, ty -> let (npatl, nvars, ni, nlins) =
    List.fold_right (fun p (patl, vars, i, lins) ->
      let (np, nvars, ni, nlins) = lin_pat p vars i lins in
      (np::patl, nvars, ni, nlins)
    ) pl ([], vars, i, lins) in
    ((MLPTuple npatl, ty), nvars, ni, nlins)
  | MLPRecord (il, pl), ty -> let (npatl, nvars, ni, nlins) =
    List.fold_right (fun p (patl, vars, i, lins) ->
      let (np, nvars, ni, nlins) = lin_pat p vars i lins in
      (np::patl, nvars, ni, nlins)
    ) pl ([], vars, i, lins) in
    ((MLPRecord (il, npatl), ty), nvars, ni, nlins)
  | MLPConstr (id, pl), ty -> let (npatl, nvars, ni, nlins) =
    List.fold_right (fun p (patl, vars, i, lins) ->
      let (np, nvars, ni, nlins) = lin_pat p vars i lins in
      (np::patl, nvars, ni, nlins)
    ) pl ([], vars, i, lins) in
    ((MLPConstr (id, npatl), ty), nvars, ni, nlins)
  | _ -> (pat, vars, i, lins)

let rec select_out_args_types types mode = match types, mode with
  | (_::tl_ty, MInput::tl_mode) -> select_out_args_types tl_ty tl_mode
  | (ty::tl_ty, MOutput::tl_mode) -> ty::(select_out_args_types tl_ty tl_mode)
  | (_::tl_ty, MSkip::tl_mode) -> select_out_args_types tl_ty tl_mode
  | _ -> []

let gen_match_term env id_extr nt = match nt with
  | NTPrem (MLTFun (a, _, None), ty) -> gen_tuple env (get_in_terms env nt)
  | NTConcl (MLTFun (pn, _, Some m), ty) 
  | NTPrem (MLTFun (pn, _, Some m), ty) ->
    let in_terms = get_in_terms env nt in
    if string_of_ident pn = "eq" && List.exists ((=) MOutput) m then
      List.hd in_terms
    else
      let fn = get_pred_name env pn m in
      let ty = if List.for_all ((!=) MOutput) m then 
        let cl, t = env.extr_hf.h_get_bool_type () in
        (CTSum (List.map ident_of_string cl), t)
      else ty in
      (MLTFun (fn, in_terms, None), ty)
(*      let spec = extr_get_spec env pn in
      let args_types =
      match pdt.pdt_pred.pred_args_types with
        | Some tyl -> 
          let typs = select_out_args_types tyl pdt.pdt_pred.pred_mode in
          begin match typs with
            | [ty] -> LFun (pn, in_terms), ty
            | [] -> LFun (pn, in_terms), (TYBool, None)
            | _ -> LFun (pn, in_terms), (TYTuple (List.map fst typs), None)
          end
        | _ -> notype (LFun (pn, in_terms)) *)
  | _ -> assert false
let gen_pat_term env nt next_term an = 
  let (pat, _, _, lins) = 
       lin_pat (gen_tuple_pat env (get_out_terms env nt) nt) [] 1 [] in
  if List.length lins > 0 then
    (pat, fake_type env (MLTMatch (fake_type env (MLTALin lins), an, 
      [(fake_type env MLPATrue, next_term, an);
       (fake_type env MLPAFalse, fake_type env MLTADefault, an)])), an)
  else
    (pat, next_term, an)

let default_case env = [(fake_type env MLPWild, fake_type env MLTADefault, [])]

let rec gen_pat env id_extr tn = match tn with
  | TreeNode (nt, tnl, an) -> gen_pat_term env nt (gen_match env id_extr tnl) an
  | TreeOutput (nt, mlt, an) -> 
    gen_pat_term env nt (gen_tuple env (get_out_terms_func env mlt)) an

and gen_match env id_extr tree = match List.hd tree with
  | TreeNode (nt, _, _) | TreeOutput (nt, _, _) ->
    let mt = gen_match_term env id_extr nt in
    let an = flatmap
      (function | TreeNode (_, _, an) | TreeOutput (_, _, an) -> an) tree in
    fake_type env (MLTMatch (mt, an, 
      (List.map (gen_pat env id_extr) tree)@(default_case env)))
    
let rec select_args_types types mode = match types, mode with
  | (ty::tl_ty, MInput::tl_mode) -> ty::(select_args_types tl_ty tl_mode)
  | (_::tl_ty, MOutput::tl_mode) -> select_args_types tl_ty tl_mode
  | (_::tl_ty, MSkip::tl_mode) -> select_args_types tl_ty tl_mode
  | _ -> []

let code_from_tree env id_tree tree = 
  let mode = List.hd (extr_get_modes env id_tree) in
  let args = gen_args mode in
  let spec = extr_get_spec env id_tree in
  let pred_args_types = spec.spec_args_types in
  let args_types = select_args_types pred_args_types mode in
  let fun_ident = get_pred_name env id_tree mode in
  let pats = List.map (gen_pat env id_tree) tree in
  let an = flatmap (fun p -> mk_an p.prop_name None) spec.spec_props in
  {
    mlfun_name = fun_ident;
    mlfun_args = args;
    mlfun_body = fake_type env (MLTMatch (gen_tuple env 
      (List.map2 (fun a t -> MLTVar a, t) args args_types),
        an, pats@(default_case env)));
  }

let make_ml_funs env =
  let ml_funs = List.map ( fun (id_tree, tree) ->
    id_tree, code_from_tree env id_tree tree ) env.extr_trees in
  { env with extr_mlfuns = ml_funs }
