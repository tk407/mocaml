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
(*  Copyright 2012 CNAM-ENSIIE                                              *)
(*                 Catherine Dubois <dubois@ensiie.fr>                      *)
(*                 David Delahaye <david.delahaye@cnam.fr>                  *)
(*                 Pierre-Nicolas Tollitte <tollitte@ensiie.fr>             *)
(****************************************************************************)


open Term
open Names
open Libnames
open Nametab
open Util
open Pp

open Pred
open Proof_scheme
open Coq_stuff
open Minimlgen
open Reltacs


let build_ind_scheme fun_name =
  let ref_func = 
    Ident (dummy_loc, id_of_string fun_name) in
  let make_fscheme () =
    Functional_principles_types.build_scheme 
      [id_of_string (fun_name ^ "_ind"), ref_func, 
       Glob_term.GProp Pos] in
  try make_fscheme () with Functional_principles_types.No_graph_found ->
    let _ = Indfun.make_graph (Nametab.global ref_func) in
    make_fscheme () 


let build_correct_lemma env id fixfun =
  let spec = extr_get_spec env id in
  let in_names = List.map string_of_ident fixfun.fixfun_args in
  let in_types = List.map get_coq_type (get_in_types (env, id)) in
  let out_name = "po" in
  let out_type = get_out_type true (env, id) in
  let func = find_coq_constr_i fixfun.fixfun_name in
  let mode = List.hd (extr_get_modes env id) in
  let full = is_full_extraction mode in
  let compl = fix_get_completion_status env fixfun.fixfun_name in
  let tru = find_coq_constr_s "Coq.Init.Datatypes.true" in
  let some = find_coq_constr_s "Coq.Init.Datatypes.Some" in
  
  (* rels for the prem definition *)
  let in_start = if full then 1 else 2 in
  let _, in_rels = List.fold_right ( fun _ (i, rels) -> 
    (i+1, (mkRel i)::rels) ) in_names (in_start, []) in
  let out_term = if full then tru 
    else if compl then mkApp (some, [|out_type; mkRel 1|]) else mkRel 1 in

  (* rels for the concl definition (the premise add 1 index) *)
  let in_start' = if full then 2 else 3 in
  let _, in_rels' = List.fold_right ( fun _ (i, rels) -> 
    (i+1, (mkRel i)::rels) ) in_names (in_start', []) in
  let out_term' = if full then [] else [mkRel 2] in

  let eq = find_coq_constr_s "Coq.Init.Logic.eq" in
  let pred = find_coq_constr_i spec.spec_name in
  let prem = 
    mkApp (eq, [|out_type; mkApp (func, Array.of_list in_rels); out_term|]) in
  let concl = mkApp (pred, Array.of_list (in_rels'@out_term')) in
  let cstr = mkProd(Anonymous, prem, concl) in
  let cstr = mkProd (Name (id_of_string out_name), out_type, cstr) in
  let cstr = List.fold_right2 ( fun n t c ->
    mkProd (Name (id_of_string n), t, c)
  ) in_names in_types cstr in
  cstr, in_names, out_name

let gen_correction_proof env id =
  let (fixfun, ps) = extr_get_fixfun env id in
  let mode = List.hd (extr_get_modes env id) in
  let compl = fix_get_completion_status env fixfun.fixfun_name in
  let full = is_full_extraction mode in

  (* functional scheme *)
  let _ = build_ind_scheme (string_of_ident fixfun.fixfun_name) in
  
  (* Lemma building *)
  let cstr, in_names, out_name = build_correct_lemma env id fixfun in

  (* Proof registering *)
  let proof_register prover ps =
    let _ = Lemmas.start_proof 
      (id_of_string (string_of_ident fixfun.fixfun_name ^ "_correct"))
      (Decl_kinds.Global, Decl_kinds.Proof (Decl_kinds.Lemma)) cstr 
      (*~init_tac:tac_name*) (fun _ _ -> ()) in
    let _ = make_proof (env, id) prover ps in
    Lemmas.save_named false in

  let ind_scheme = (string_of_ident fixfun.fixfun_name ^ "_ind") in

  if (not compl) && (not full) then
    proof_register simple_pc ps
  else
    ()


