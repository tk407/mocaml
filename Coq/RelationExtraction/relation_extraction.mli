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

(* Print a string to the extraction file. *)
val extraction_print : string -> unit

(* Extraction of one relation (or mutually recursive relations). *)
val relation_extraction_single : Libnames.reference ->
  (Libnames.reference * int list) list -> unit
val relation_extraction : Libnames.reference ->
  (Libnames.reference * int list) list -> unit

(* Extraction of one relation from a non deterministic specification. *)
val relation_extraction_single_order : Libnames.reference ->
  (Libnames.reference * int list) list -> unit
val relation_extraction_order : Libnames.reference ->
  (Libnames.reference * int list) list -> unit

(* Extraction of one or more relations into Fixpoints. *)
val relation_extraction_fixpoint : Libnames.reference ->
  (Libnames.reference * int list) list -> recursion_style option -> unit

val relation_extraction_fixpoint_order : Libnames.reference ->
  (Libnames.reference * int list) list -> recursion_style option -> unit
