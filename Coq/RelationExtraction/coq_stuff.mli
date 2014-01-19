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
open Pred

(* Coq types. *)
type htyp = Term.types option

(* Coq environment. *)
type henv = {
  ind_refs : (ident * Libnames.reference) list;
  ind_grefs : (ident * Libnames.global_reference) list;
  cstrs : (ident * Term.constr) list;
}

(* Functions to manipulate Coq data. *)
val coq_functions : (htyp, henv) host_functions

(* Extraction of dependencies *)
val extract_dependencies : henv -> unit

(*********)
(* Utils *)
(*********)

(* Mode adapter for parameters. Must be used on all modes given by the user. *)
val adapt_mode : Libnames.reference -> int list -> int list

(* Mode conversion, with skipers for implicit arguments. 
   If the mode is not provided, it returns the full mode.
   adapt_mode may be invoked prior to this function. *)
val make_mode : Libnames.global_reference -> (int list) option -> mode

(* Get the type of the arguments of an extracted function. *)
val get_in_types : (htyp, henv) extract_env * ident -> htyp term_type list

(* Gets the output type of an extracted function,
   ignoring the eventual completion with the type option when opt is false. *)
val get_out_type : bool -> (htyp, henv) extract_env * ident -> Term.types

(* Gets the Coq type from a term_type. *)
val get_coq_type : htyp term_type -> Term.types

(* Find a Coq constr from its name (as an ident or a string) *)
val find_coq_constr_i : ident -> Term.constr
val find_coq_constr_s : string -> Term.constr


(* Prints a Coq constr. *)
val pp_coq_constr : Term.constr -> string

