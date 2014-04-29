Add ML Path "Coq/RelationExtraction".
Print LoadPath.
Declare ML Module "relation_extraction_plugin".

Require Import Arith.
Require Import Bool.
Require Import Sumbool.
Require Import List.
Require Import Classical_Prop.

Load mconbase2.



(* Extractable version of is_value_of_expr *)
Fixpoint xis_value_of_expr (e_5:expr) : bool :=
  match e_5 with
  | (E_ident value_name5) => false
  | (E_constant constant5) => (true)
  | (E_apply (E_constant (CONST_fork)) e) => ((xis_value_of_expr e))
  | (E_apply (E_constant (CONST_pair)) e) => ((xis_value_of_expr e))
  | (E_apply expr5 expr') => match expr5 with | E_constant (CONST_fork) => xis_value_of_expr (expr') | E_constant (CONST_pair) => xis_value_of_expr (expr') | _ => false end  
  | (E_bind expr5 expr') => false
  | (E_function value_name5 typexpr5 expr5) => true
  | (E_fix e) => false
  | (E_live_expr expr5) => true
  | (E_pair e e') => (if (xis_value_of_expr e) then (xis_value_of_expr e') else false)
  | (E_taggingleft e) => ((xis_value_of_expr e))
  | (E_taggingright e) => ((xis_value_of_expr e))
  | (E_case e1 x1 e2 x2 e3) => false
end.

(*
Fixpoint xis_forkvalue (e : expr) : bool :=
  match e with
  | (E_ident value_name5) => false
  | (E_constant constant5) => match constant5 with | CONST_fork => false | CONST_ret => true | CONST_unit => false | CONST_stop => true end
  | (E_apply (E_constant (CONST_fork)) e) => ((xis_value_of_expr e))
  | (E_apply expr5 expr') => false
  | (E_bind expr5 expr') => false
  | (E_function value_name5 typexpr5 expr5) => false
  | (E_fix e) => (xis_value_of_expr e)
  | (E_live_expr lm) => match lm with | LM_comp => false | LM_expr e' => (xis_value_of_expr e') end
  | (E_pair e e') => false
  | (E_taggingleft e) => false
  | (E_taggingright e) => false
  | (E_case e1 x1 e2 x2 e3) => false
end. *)

(* Proof that is_value_of_expr and xis_value_of_expr are equivalent *)

CoInductive selectstar : Set := Seq : select -> selectstar -> selectstar.

Recursive Extraction selectstar.

(* Extractable version of the reduction operation *)
Inductive XJO_red : expr -> selectstar -> expr -> Prop :=    (* defn red *)
(* | XJO_red_app : forall (x:value_name) (t : typexpr) (e v:expr) (s:selectstar),
     (eq (xis_value_of_expr v) true) ->
     XJO_red (E_apply  (E_function x t e)  v) s  (subst_expr  v   x   e ) 
 | XJO_red_ret : forall (v:expr) (s:selectstar),
     (eq (xis_value_of_expr v) true) ->
     XJO_red (E_apply (E_constant CONST_ret) v) s (E_live_expr (LM_expr (v))) 
 | XJO_red_evalbind : forall (e e'' e':expr) (s:selectstar),
    (eq (xis_value_of_expr e) false) ->
     XJO_red e s e' ->
     XJO_red (E_bind e e'') s (E_bind e' e'')
 | XJO_red_movebind : forall (e e'' e':expr) (s:selectstar),
     (eq (xis_value_of_expr e) false) -> 
     XJO_red e s e' ->
     XJO_red (E_bind  (E_live_expr (LM_expr (e)))  e'') s (E_bind  (E_live_expr (LM_expr (e')))  e'')
 | XJO_red_dobind : forall (v e:expr) (s:selectstar),
     (eq (xis_value_of_expr v) true) ->
     XJO_red (E_bind  (E_live_expr (LM_expr (v)))  e) s (E_apply e v) 
 | XJO_red_compbind : forall (l:label) (e:expr) (s:selectstar),
     XJO_red (E_bind  (E_live_expr (LM_comp (l)))  e) s (E_apply e (E_constant CONST_unit)) 
 | XJO_red_inpair : forall (v v':expr) (s:selectstar),
     (eq (xis_value_of_expr v) true) ->
     (eq (xis_value_of_expr v') true) ->
     XJO_red (E_apply  (E_apply (E_constant CONST_pair) v)  v') s (E_pair v v') *)
 | XJO_red_proj1 : forall (v v':expr) (s:selectstar),
     (eq (xis_value_of_expr v) true) ->
     (eq (xis_value_of_expr v') true) ->
     XJO_red (E_apply (E_constant CONST_proj1) (E_pair v v')) s v
 | XJO_red_proj2 : forall (v v':expr) (s:selectstar),
     (eq (xis_value_of_expr v) true) ->
     (eq (xis_value_of_expr v') true) ->
     XJO_red (E_apply (E_constant CONST_proj2) (E_pair v v')) s  v'
 | XJO_red_forkdeath1 : forall (e:expr) (lm : livemodes) (s:selectstar),
     (eq (xis_value_of_expr e) true) ->
     XJO_red (E_apply  (E_apply (E_constant CONST_fork)  (E_live_expr (LM_expr (e))) )   (E_live_expr (lm)) ) (Seq S_First s) (E_live_expr (LM_expr(E_taggingleft (E_pair e  (E_live_expr lm)) )))
 | XJO_red_forkmove1 : forall (e e':expr) (lm : livemodes) (s:selectstar),
     (eq (xis_value_of_expr e) false) ->
     XJO_red e s e' -> 
     XJO_red (E_apply  (E_apply (E_constant CONST_fork)  (E_live_expr (LM_expr (e))) )   (E_live_expr (lm)) ) (Seq S_First s) (E_apply  (E_apply (E_constant CONST_fork)  (E_live_expr (LM_expr (e'))) )   (E_live_expr (lm)) ) 
 | XJO_red_forkdeath2 : forall (e:expr) (lm : livemodes) (s:selectstar),
     (eq (xis_value_of_expr e) true) ->
     XJO_red (E_apply  (E_apply (E_constant CONST_fork)  (E_live_expr (lm)) )   (E_live_expr (LM_expr (e))) ) (Seq S_Second s) (E_live_expr (LM_expr(E_taggingright (E_pair   (E_live_expr lm) e) )))
 | XJO_red_forkmove2 : forall (e e':expr) (lm : livemodes) (s:selectstar),
     (eq (xis_value_of_expr e) false) ->
     XJO_red e s e' -> 
     XJO_red (E_apply  (E_apply (E_constant CONST_fork)  (E_live_expr (lm)) )   (E_live_expr (LM_expr (e))) ) (Seq S_Second s) (E_apply  (E_apply (E_constant CONST_fork)  (E_live_expr (lm)) )   (E_live_expr (LM_expr (e'))) ) 
 | XJO_red_forkdocomp1 : forall (l:label) (lm : livemodes) (s:selectstar),
     XJO_red (E_apply  (E_apply (E_constant CONST_fork)  (E_live_expr (LM_comp (l))) )   (E_live_expr (lm)) ) (Seq S_First s) (E_live_expr (LM_expr(E_taggingleft (E_pair (E_constant CONST_unit)  (E_live_expr lm)) )))
 | XJO_red_forkdocomp2 : forall (l:label) (lm : livemodes) (s:selectstar),
     XJO_red (E_apply  (E_apply (E_constant CONST_fork)  (E_live_expr (lm)) )   (E_live_expr (LM_comp (l))) ) (Seq S_Second s) (E_live_expr (LM_expr(E_taggingright (E_pair   (E_live_expr lm) (E_constant CONST_unit)) )))
| XJO_red_context_app1 : forall (e e' e'':expr) (s:selectstar),
     (eq (xis_value_of_expr e) false) ->
     XJO_red e s e'' ->
     XJO_red (E_apply e e') s (E_apply e'' e')
 | XJO_red_context_app2 : forall (e' v e'':expr) (s:selectstar),
     (eq (xis_value_of_expr v) true) ->
     XJO_red e' s e'' ->
     XJO_red (E_apply v e') s (E_apply v e'')  
(* | XJO_red_fix_move : forall (e e':expr) (s:selectstar),
     XJO_red e s e' -> 
     XJO_red (E_fix  e) s (  (E_fix e'))
 | XJO_red_fix_app : forall (e:expr) (x:value_name)(t:typexpr) (s:selectstar),
     XJO_red ( (E_fix  (E_function x t e))) s (subst_expr  (E_fix  (E_function x t e))   x   e)
 | XJO_red_pair_1 : forall (e e'' e':expr) (s:selectstar),
     (eq (xis_value_of_expr e) false) ->
     XJO_red e s e' ->
     XJO_red (E_pair e e'') s (E_pair e' e'')
 | XJO_red_pair_2 : forall (v e e':expr)(s s':selectstar),
     (eq (xis_value_of_expr v) true) ->
     XJO_red e s e' ->
     XJO_red (E_pair v e) s' (E_pair v e')
 | XJO_red_evalinl : forall (e e':expr)(s:selectstar),
     XJO_red e s e' ->
     XJO_red (E_taggingleft e) s (E_taggingleft e')
 | XJO_red_evalinr : forall (e e':expr) (s:selectstar),
     XJO_red e s e' ->
     XJO_red (E_taggingright e) s (E_taggingright e')
 | XJO_red_evalcaseinl : forall (x:value_name) (e:expr) (x':value_name) (e' v:expr)(s:selectstar),
     (eq (xis_value_of_expr v) true) ->
     XJO_red (E_case  (E_taggingleft v)  x e x' e') s  (subst_expr  v   x   e ) 
 | XJO_red_evalcaseinr : forall (x:value_name) (e:expr) (x':value_name) (e' v:expr)(s:selectstar),
     (eq (xis_value_of_expr v) true) ->
     XJO_red (E_case  (E_taggingright v)  x e x' e') s  (subst_expr  v   x'   e' ) 
 | XJO_red_evalcase : forall (e:expr) (x:value_name) (e'':expr) (x':value_name) (e''' e':expr) (s:selectstar),
     (eq (xis_value_of_expr e) false) ->
     XJO_red e s e' ->
     XJO_red (E_case e x e'' x' e''') s (E_case e' x e'' x' e''')*).  


(*Extraction Relation Fixpoint is_expr_of_expr [1]. *)

Recursive Extraction xis_value_of_expr.

Recursive Extraction select.

Recursive Extraction expr.

 Extract Inductive bool => "bool" [ "true" "false" ].

Extract Inductive nat => int [ "0" "succ" ] "(fun fO fS n -> if n=0 then fO () else fS (n-1))".

Extract Inductive sumbool => "bool" [ "true" "false" ].

Extract Inductive list => "list" [ "[]" "(::)" ].

Extract Inductive prod => "(*)"  [ "(,)" ].


Extraction Relation Relaxed XJO_red [1 1 2].


(* Extraction Relation G_constant [1 2]. *)