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
(*  Copyright 2011 CNAM-ENSIIE                                              *)
(*                 Catherine Dubois <dubois@ensiie.fr>                      *)
(*                 David Delahaye <david.delahaye@cnam.fr>                  *)
(*                 Pierre-Nicolas Tollitte <tollitte@ensiie.fr>             *)
(****************************************************************************)


(*i camlp4deps: "parsing/grammar.cma" i*)

open Genarg
open Pp
open Relation_extraction

let pr_mode _ _ _ (id, mode) =
  str "" ++ spc () ++ str "[" ++
     (List.fold_left (fun b e -> b ++ spc () ++ int e) (mt ()) mode) ++
     spc () ++ str "]"

ARGUMENT EXTEND mode
  TYPED AS reference * (int list)
  PRINTED BY pr_mode
  | [ global(id) "[" integer_list(mde) "]" ] -> [ (id, mde) ]
END

let pr_rec_style rs = match rs with
  | Some (Pred.StructRec i) -> 
    str "" ++ spc () ++ str "Struct" ++ spc () ++ int i
  | Some Pred.FixCount -> 
    str "" ++ spc () ++ str "Counter"
  | None -> str ""

VERNAC ARGUMENT EXTEND rec_style
PRINTED BY pr_rec_style
  | [ "Struct" integer(i) ] -> [ Some (Pred.StructRec i) ]
  | [ "Counter" ] -> [ Some Pred.FixCount ]
  | [] -> [ None ]
END


VERNAC COMMAND EXTEND ExtractionRelation
| [ "Extraction" "Relation" mode(mde) ] ->
  [ relation_extraction (fst mde) [ mde ] ]
| [ "Extraction" "Relation" mode(mde) "with" mode_list(modes) ] ->
  [ relation_extraction (fst mde) (mde :: modes) ]
END

VERNAC COMMAND EXTEND ExtractionRelationRelaxed
| [ "Extraction" "Relation" "Relaxed" mode(mde) ] ->
  [ relation_extraction_order (fst mde) [ mde ] ]
| [ "Extraction" "Relation" "Relaxed" mode(mde) "with" mode_list(modes) ] ->
  [ relation_extraction_order (fst mde) (mde :: modes) ]
END

VERNAC COMMAND EXTEND ExtractionRelationSingle
| [ "Extraction" "Relation" "Single" mode(mde) ] ->
  [ relation_extraction_single (fst mde) [ mde ] ]
| [ "Extraction" "Relation" "Single" mode(mde) "with" mode_list(modes) ] ->
  [ relation_extraction_single (fst mde) (mde :: modes) ]
END

VERNAC COMMAND EXTEND ExtractionRelationSingleRelaxed
| [ "Extraction" "Relation" "Single" "Relaxed" mode(mde) ] ->
  [ relation_extraction_single_order (fst mde) [ mde ] ]
| [ "Extraction" "Relation" "Single" "Relaxed" mode(mde) "with" mode_list(modes) ] ->
  [ relation_extraction_single_order (fst mde) (mde :: modes) ]
END


VERNAC COMMAND EXTEND ExtractionRelationFixpoint
| [ "Extraction" "Relation" "Fixpoint" mode(mde) rec_style(recs) ] ->
  [ relation_extraction_fixpoint (fst mde) [ mde ] (recs) ]
| [ "Extraction" "Relation" "Fixpoint" mode(mde) rec_style(recs) "with" mode_list(modes) ] ->
  [ relation_extraction_fixpoint (fst mde) (mde :: modes) (recs) ]
END

VERNAC COMMAND EXTEND ExtractionRelationFixpointRelaxed
| [ "Extraction" "Relation" "Fixpoint" "Relaxed" mode(mde) rec_style(recs) ] ->
  [ relation_extraction_fixpoint_order (fst mde) [ mde ] (recs) ]
| [ "Extraction" "Relation" "Fixpoint" "Relaxed" mode(mde) rec_style(recs) "with" mode_list(modes) ] ->
  [ relation_extraction_fixpoint_order (fst mde) (mde :: modes) (recs) ]
END


