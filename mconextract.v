Add ML Path "Coq/RelationExtraction".
Print LoadPath.
Declare ML Module "relation_extraction_plugin".

Require Import Arith.
Require Import Bool.
Require Import Sumbool.
Require Import List.
Require Import Classical_Prop.

Load progress.



(* Extractable version of is_value_of_expr *)
Fixpoint xis_value_of_expr (e_5:expr) : bool :=
  match e_5 with
  | (E_ident value_name5) => false
  | E_unit => (true)
  | (E_apply expr5 expr') => false
  | (E_bind expr5 expr') => false
  | (E_function value_name5 typexpr5 expr5) => (true)
  | (E_fix e) => false
  | (E_comp e) => false
  | (E_live_expr e) => (true)
  | (E_pair e e') => (if (xis_value_of_expr e) then (xis_value_of_expr e') else false)
  | (E_inpair e e') => false
  | (E_proj1 e) => false
  | (E_proj2 e) => false
  | (E_fork e e') => false
  | (E_ret e) => false
  | (E_taggingleft e) => ((xis_value_of_expr e))
  | (E_taggingright e) => ((xis_value_of_expr e))
  | (E_case e1 x1 e2 x2 e3) => false
end.


(* Proof that is_value_of_expr and xis_value_of_expr are equivalent *)

Lemma label_det_by_star_dest_select : forall (e e' : expr) (s : select) (rl : redlabel), e [ s ] --> [ rl ] e' -> (forall (rl' : redlabel), e [ s ] --> [ rl' ] e' -> rl=rl').
Proof. 
 Check JO_red_ind.
 intros.
 Hint Resolve red_not_value.
 induction H; substs; inversion H0; substs; intuition; eauto.
 apply red_not_value in H7; contradiction.
 apply red_not_value in H5; simpl in H5; intuition.
 (* FORK *)
 apply red_not_value in H; contradiction.
 apply red_not_value in H; simpl in H; intuition.
 apply red_not_value in H; simpl in H; intuition.
 apply red_not_value in H6; contradiction.
 apply red_not_value in H1; simpl in H1; intuition.
 apply red_not_value in H1; simpl in H1; intuition.
 apply red_not_value in H6; simpl in H6; intuition.
 apply red_not_value in H9; simpl in H9; intuition.

 (* FORK *)


 apply red_not_value in H6; simpl in H6; intuition.
 apply red_not_value in H8; simpl in H8; intuition.
 (* FORK *)
 apply red_not_value in H; simpl in H; intuition.
 apply red_not_value in H5; simpl in H5; intuition.
 (* SUBST ! *)
 apply red_not_value in H1; contradiction.
 apply red_not_value in H6; contradiction.
 apply red_not_value in H; simpl in H; intuition.
 apply red_not_value in H; contradiction.
 apply red_not_value in H; simpl in H; intuition.
 apply red_not_value in H4; simpl in H4; intuition.
 apply red_not_value in H; contradiction.
 apply red_not_value in H6; contradiction.
 apply red_not_value in H; contradiction.
 apply red_not_value in H6; contradiction.
 inversion H8.
 apply red_not_value in H2; contradiction.
 inversion H8.
 apply red_not_value in H2; contradiction.
 inversion H.
 apply red_not_value in H2; contradiction.
 inversion H.
 apply red_not_value in H2; contradiction.
Qed.



CoInductive selectstar : Set := Seq : select -> selectstar -> selectstar.

Recursive Extraction selectstar.

(* Extractable version of the reduction operation *)
Inductive XJO_red : expr -> select -> expr -> Prop :=    (* defn red *)
| XJO_red_app : forall (x:value_name) (t : typexpr) (e v:expr) (s:select),
     (eq (xis_value_of_expr v) true) ->
     XJO_red (E_apply  (E_function x t e)  v) s  (subst_expr  v   x   e ) 
 | XJO_red_ret : forall (v:expr) (s:select),
     (eq (xis_value_of_expr v) true) ->
     XJO_red (E_ret v) s (E_live_expr ( (v))) 
 | XJO_red_evalret : forall (v v':expr) (s:select),
     (eq (xis_value_of_expr v) false) ->
     XJO_red v s v' ->
     XJO_red (E_ret v) s  (E_ret v') 
 | XJO_red_evalbind : forall (e e'' e':expr) (s:select),
    (eq (xis_value_of_expr e) false) ->
     XJO_red e s e' ->
     XJO_red (E_bind e e'') s (E_bind e' e'')
 | XJO_red_movebind : forall (e e'' e':expr) (s:select),
     (eq (xis_value_of_expr e) false) -> 
     XJO_red e s e' ->
     XJO_red (E_bind  (E_live_expr ( (e)))  e'') s (E_bind  (E_live_expr ( (e')))  e'')
 | XJO_red_dobind : forall (v e:expr) (s:select),
     (eq (xis_value_of_expr v) true) ->
     XJO_red (E_bind  (E_live_expr ( (v)))  e) s (E_apply e v)  
 | XJO_red_inpair : forall (v v':expr) (s:select),
     (eq (xis_value_of_expr v) true) ->
     (eq (xis_value_of_expr v') true) ->
     XJO_red (E_inpair v  v') s (E_pair v v')
 | XJO_red_inpair_eval2 : forall (v v' v'' :expr) (s:select),
     (eq (xis_value_of_expr v) true) ->
     (eq (xis_value_of_expr v') false) ->
     XJO_red v' s v'' ->
     XJO_red (E_inpair v  v') s (E_inpair v v'')  
 | XJO_red_inpair_eval1 : forall (v v' v'' :expr) (s:select),
     (eq (xis_value_of_expr v) false) ->
     XJO_red v s v'' ->
     XJO_red (E_inpair v  v') s (E_inpair v'' v') 
 | XJO_red_docomp : forall (e:expr) (s:select),
     XJO_red (E_comp e) s e
 | XJO_red_proj1 : forall (v v':expr) (s:select),
     (eq (xis_value_of_expr v) true) ->
     (eq (xis_value_of_expr v') true) ->
     XJO_red (E_proj1 (E_pair v v')) s v
 | XJO_red_proj1_eval : forall (v v':expr) (s:select),
     (eq (xis_value_of_expr v) false) ->
     XJO_red v s v' -> 
     XJO_red (E_proj1 v) s  (E_proj1 v')
 | XJO_red_proj2 : forall (v v':expr) (s:select),
     (eq (xis_value_of_expr v) true) ->
     (eq (xis_value_of_expr v') true) ->
     XJO_red (E_proj2 (E_pair v v')) s  v'
 | XJO_red_proj2_eval : forall (v v':expr) (s:select),
     (eq (xis_value_of_expr v) false) ->
     XJO_red v s v' -> 
     XJO_red (E_proj2 v) s  (E_proj2 v')
 
 | XJO_red_forkeval1 : forall (e e':expr) (s:select) (rl:redlabel) (e'':expr),
     (eq (xis_value_of_expr e) false) ->
     XJO_red e s e'' ->
     XJO_red (E_fork e e') s (E_fork e'' e')
 | XJO_red_forkeval2 : forall (v e':expr) (s:select) (rl:redlabel) (e'':expr),
     (eq (xis_value_of_expr v) true) ->
     (eq (xis_value_of_expr e') false) ->
     XJO_red e' s e'' ->
     XJO_red (E_fork v e') s (E_fork v e'')
 | XJO_red_forkmove1 : forall (e e':expr)  (e'':expr) (s:select),
     (eq (xis_value_of_expr e) false) ->
     (eq (xis_value_of_expr e') false) ->
     XJO_red e s e'' ->
     XJO_red (E_fork  (E_live_expr e)   (E_live_expr e') ) (S_Seq SO_First s) (E_fork  (E_live_expr e'')   (E_live_expr e') )
 | XJO_red_forkmove2 : forall (e e':expr)  (e'':expr) (s:select),
     (eq (xis_value_of_expr e) false) ->
     (eq (xis_value_of_expr e') false) ->
     XJO_red e' s e'' ->
     XJO_red (E_fork  (E_live_expr e)  (E_live_expr e') ) (S_Seq SO_Second s) (E_fork  (E_live_expr e)    (E_live_expr e'') )
 | XJO_red_forkdeath1 : forall (v e:expr) (s : select),
     (eq (xis_value_of_expr v) true) ->
     XJO_red (E_fork  (E_live_expr v)    (E_live_expr e) ) s (E_live_expr  (E_taggingleft   (E_pair v  (E_live_expr e) )  ) )
 | XJO_red_forkdeath2 : forall (e v':expr) (s : select),
     (eq (xis_value_of_expr v') true) ->
     XJO_red (E_fork  (E_live_expr e)    (E_live_expr v') ) s (E_live_expr  (E_taggingright  (E_pair  (E_live_expr e)  v') ) )
 | XJO_red_context_app1 : forall (e e' e'':expr) (s:select),
     (eq (xis_value_of_expr e) false) ->
     XJO_red e s e'' ->
     XJO_red (E_apply e e') s (E_apply e'' e')
 | XJO_red_context_app2 : forall (e' v e'':expr) (s:select),
     (eq (xis_value_of_expr v) true) ->
     XJO_red e' s e'' ->
     XJO_red (E_apply v e') s (E_apply v e'')  
 | XJO_red_fix_move : forall (e e':expr) (s:select),
     XJO_red e s e' -> 
     XJO_red (E_fix  e) s (  (E_fix e'))
 | XJO_red_fix_app : forall (e:expr) (x:value_name)(t:typexpr) (s:select),
     XJO_red ( (E_fix  (E_function x t e))) s (subst_expr  (E_fix  (E_function x t e))   x   e)
 | XJO_red_pair_1 : forall (e e'' e':expr) (s:select),
     (eq (xis_value_of_expr e) false) ->
     XJO_red e s e' ->
     XJO_red (E_pair e e'') s (E_pair e' e'')
 | XJO_red_pair_2 : forall (v e e':expr)(s:select),
     (eq (xis_value_of_expr v) true) ->
     XJO_red e s e' ->
     XJO_red (E_pair v e) s (E_pair v e')
 | XJO_red_evalinl : forall (e e':expr)(s:select),
     XJO_red e s e' ->
     XJO_red (E_taggingleft e) s (E_taggingleft e')
 | XJO_red_evalinr : forall (e e':expr) (s:select),
     XJO_red e s e' ->
     XJO_red (E_taggingright e) s (E_taggingright e')
 | XJO_red_evalcaseinl : forall (x:value_name) (e:expr) (x':value_name) (e' v:expr)(s:select),
     (eq (xis_value_of_expr v) true) ->
     XJO_red (E_case  (E_taggingleft v)  x e x' e') s  (subst_expr  v   x   e ) 
 | XJO_red_evalcaseinr : forall (x:value_name) (e:expr) (x':value_name) (e' v:expr)(s:select),
     (eq (xis_value_of_expr v) true) ->
     XJO_red (E_case  (E_taggingright v)  x e x' e') s  (subst_expr  v   x'   e' ) 
 | XJO_red_evalcase : forall (e:expr) (x:value_name) (e'':expr) (x':value_name) (e''' e':expr) (s:select),
     (eq (xis_value_of_expr e) false) ->
     XJO_red e s e' ->
     XJO_red (E_case e x e'' x' e''') s (E_case e' x e'' x' e''') .  


(*Extraction Relation Fixpoint is_expr_of_expr [1]. *)
(*
Extract Inductive bool => "bool" [ "true" "false" ].

Extract Inductive nat => int [ "0" "succ" ] "(fun fO fS n -> if n=0 then fO () else fS (n-1))".

Extract Inductive sumbool => "bool" [ "true" "false" ].

Extract Inductive list => "list" [ "[]" "(::)" ].

Extract Inductive prod => "(*)"  [ "(,)" ].

Recursive Extraction xis_value_of_expr.

Recursive Extraction subst_expr.

Recursive Extraction select.

Recursive Extraction expr.
*)

Lemma is_xis_val_equiv : forall (e : expr), is_value_of_expr e <-> (eq (xis_value_of_expr e) true).
 intros.
 induction e; intuition.
 simpl in H.
 simpl.
 trivial.
 simpl; trivial.
 simpl; trivial.
 intuition.
 simpl.
 simpl in H3.
 intuition.
 rewrite -> H3; rewrite -> H; simpl; reflexivity.
 simpl; simpl in H3; destruct (xis_value_of_expr e1); destruct (xis_value_of_expr e2); simpl in H3; intuition.
Qed.

Lemma is_xis_val_equiv_neg : forall (e : expr), (~(is_value_of_expr e)) <-> (eq (xis_value_of_expr e) false).
Proof.
 intros.
 rewrite is_xis_val_equiv.
 intuition.
 destruct (xis_value_of_expr e); intuition.
 congruence.
Qed.

Hint Resolve is_xis_val_equiv.
Hint Resolve is_xis_val_equiv_neg.

Lemma JO_then_xJO : forall (e e' : expr) (s : select) (rl : redlabel), e [ s ] --> [ rl ] e' -> XJO_red e s e'.
Proof.
 Hint Constructors JO_red.
 Hint Constructors XJO_red.
 intros.
 induction H; intuition. 
 apply is_xis_val_equiv in H; apply XJO_red_app; intuition.
 apply XJO_red_forkeval1; intuition; apply red_not_value in H; apply is_xis_val_equiv_neg in H; assumption.
 apply XJO_red_forkeval2; intuition.
 apply is_xis_val_equiv in H.
 assumption.
 apply red_not_value in H0.
 apply is_xis_val_equiv_neg in H0.
 assumption.
 apply XJO_red_forkmove1.
 Hint Resolve red_not_value.
 apply red_not_value in H.
 apply is_xis_val_equiv_neg in H.
 assumption.
 apply is_xis_val_equiv_neg in H0; assumption.
 assumption.
 apply XJO_red_forkmove2.
 Hint Resolve red_not_value.
 apply red_not_value in H.
 apply is_xis_val_equiv_neg in H.
 apply is_xis_val_equiv_neg in H0; assumption.
 apply red_not_value in H.
 apply is_xis_val_equiv_neg in H; assumption.
 assumption.
 apply XJO_red_forkdeath1.
 Hint Rewrite is_xis_val_equiv.
 apply is_xis_val_equiv.
 assumption.
 apply XJO_red_forkdeath2.
 Hint Rewrite is_xis_val_equiv.
 apply is_xis_val_equiv.
 assumption.
 apply XJO_red_ret.
 apply is_xis_val_equiv.
 assumption.
 apply red_not_value in H.
 apply is_xis_val_equiv_neg in H.
 apply XJO_red_evalret; intuition.
 apply red_not_value in H.
 apply is_xis_val_equiv_neg in H.
 apply XJO_red_evalbind; intuition.
 apply red_not_value in H.
 apply is_xis_val_equiv_neg in H.
 apply XJO_red_movebind; intuition.
 apply is_xis_val_equiv in H.
 apply XJO_red_dobind; intuition.
 apply red_not_value in H0; apply is_xis_val_equiv_neg in H0; apply XJO_red_context_app2; intuition.
 apply is_xis_val_equiv in H; assumption.
 apply red_not_value in H; apply is_xis_val_equiv_neg in H; apply XJO_red_context_app1; intuition.
  apply red_not_value in H; apply is_xis_val_equiv_neg in H; apply XJO_red_pair_1; intuition.
 apply red_not_value in H0; apply is_xis_val_equiv_neg in H0; apply XJO_red_pair_2; intuition.
 apply is_xis_val_equiv in H; assumption.
 apply is_xis_val_equiv in H0; apply XJO_red_inpair; intuition; apply is_xis_val_equiv in H; assumption.
 apply red_not_value in H; apply is_xis_val_equiv_neg in H; apply XJO_red_inpair_eval1; intuition.
 apply red_not_value in H0; apply is_xis_val_equiv_neg in H0; apply XJO_red_inpair_eval2; intuition;
 apply is_xis_val_equiv in H; assumption.
 apply is_xis_val_equiv in H0; apply XJO_red_proj1; intuition; apply is_xis_val_equiv in H; assumption.
 apply is_xis_val_equiv in H0; apply XJO_red_proj2; intuition; apply is_xis_val_equiv in H; assumption.
 apply red_not_value in H; apply is_xis_val_equiv_neg in H; apply XJO_red_proj1_eval; intuition.
 apply red_not_value in H; apply is_xis_val_equiv_neg in H; apply XJO_red_proj2_eval; intuition.
 apply is_xis_val_equiv in H; apply XJO_red_evalcaseinl; intuition.
 apply is_xis_val_equiv in H; apply XJO_red_evalcaseinr; intuition.
 apply red_not_value in H; apply is_xis_val_equiv_neg in H; apply XJO_red_evalcase; intuition.
Qed.

Lemma xJO_then_JO : forall (e e' : expr) (s : select),XJO_red e s e' -> (exists (rl : redlabel), e [ s ] --> [ rl ] e').
Proof.
 Hint Constructors JO_red.
 Hint Constructors XJO_red.
 intros.
 induction H; intuition; try solve [ auto | jauto |
    apply is_xis_val_equiv in H; exists RL_tau; intuition | 
    apply is_xis_val_equiv_neg in H; destruct IHXJO_red as [rl L]; exists rl; intuition |
    apply is_xis_val_equiv in H; destruct IHXJO_red as [rl L]; exists rl; intuition |
    apply is_xis_val_equiv in H; apply is_xis_val_equiv in H0; exists RL_tau; intuition |
    apply is_xis_val_equiv in H; apply is_xis_val_equiv_neg in H0; destruct IHXJO_red as [rl L]; exists rl; intuition |
    apply is_xis_val_equiv in H; apply is_xis_val_equiv_neg in H0; destruct IHXJO_red as [rl' L]; exists rl'; intuition |
    apply is_xis_val_equiv_neg in H; apply is_xis_val_equiv_neg in H0; destruct IHXJO_red as [rl L]; exists rl; intuition].
Qed.

Extraction selectstar.

Extraction Relation Relaxed XJO_red [1 1 2].

Recursive Extraction is_value_of_expr.



(* Extraction Relation G_constant [1 2]. *)