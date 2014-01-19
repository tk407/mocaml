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

(* Proof scheme declaration *)

type pident = {
  pi_func_name : string;
  pi_spec_name : string option;
}

type prem_orig = {
  po_prem_name : string;
}

type 't ps_atom =
  | LetVar of (pident * 't * prem_orig)
  | CaseConstr of ('t * string * pident list * prem_orig)
  | LetDum of (pident * 't)
  | CaseDum of ('t * string * pident list)
  | OutputTerm of 't option

type 't ps_branch = {
  psb_prop_name : string option;
  psb_branch : ('t ps_atom * string option) list;
}

type 't proof_scheme = {
  scheme_branches : 't ps_branch list;
}

let rec concat_list l sep = match l with
  | [] -> ""
  | [a] -> a
  | a::tl -> a ^ sep ^ (concat_list tl sep)

let pp_pident pi = match pi.pi_spec_name with
  | None -> pi.pi_func_name
  | Some s -> pi.pi_func_name ^ "{" ^ s ^ "}"

let pp_proof_scheme pp_t ps = concat_list (List.map (fun b ->
    begin match b.psb_prop_name with
      | Some pn -> pn
      | None -> "%default%" end ^ ": " ^
    concat_list (List.map (fun (a, _) -> match a with
      | LetVar (pi, t, po) -> "LetVar (" ^ pp_pident pi ^ ", " ^ pp_t t ^ ", " ^ 
         po.po_prem_name ^ ")"
      | LetDum (pi, t) -> "LetDum (" ^ pp_pident pi ^ ", " ^ pp_t t ^ ")"
      | CaseConstr (t, s, pil, po) -> "CaseConstr (" ^ pp_t t ^ ", " ^ s ^ ", (" ^ 
         concat_list (List.map pp_pident pil) ", " ^ "), " ^ po.po_prem_name ^ ")"
      | CaseDum (t, s, pil) -> "CaseDum (" ^ pp_t t ^ ", " ^ s ^ ", (" ^ 
         concat_list (List.map pp_pident pil) ", " ^ "))"
      | OutputTerm (Some t) -> "OutputTerm (" ^ pp_t t ^ ")"
      | OutputTerm (None) -> "OutputTerm (None)"
    ) b.psb_branch) " -> "
  ) ps.scheme_branches) "\n"



