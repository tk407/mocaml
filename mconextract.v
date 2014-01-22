Add ML Path "Coq/RelationExtraction".
Print LoadPath.
Declare ML Module "relation_extraction_plugin".

Load mconbase.

Inductive selectSet : Set := 
 | First : selectSet
 | Second : selectSet
 | Both : selectSet.

Axiom select : selectSet.

Extract Constant select => "(selectBranch)".


(** subrules *)
Fixpoint xis_value_of_expr (e_5:expr) : bool :=
  match e_5 with
  | (E_ident value_name5) => false
  | (E_constant constant5) => (true)
  | (E_apply expr5 expr') => false
  | (E_bind expr5 expr') => false
  | (E_function value_name5 typexpr5 expr5) => true
  | (E_live_expr expr5) => true
  | (E_pair e e') => (if (xis_value_of_expr e) then (xis_value_of_expr e') else false)
  | (E_taggingleft e) => ((xis_value_of_expr e))
  | (E_taggingright e) => ((xis_value_of_expr e))
  | (E_case e1 x1 e2 x2 e3) => false
end.

Lemma l_val : forall (e:expr), (eq (xis_value_of_expr e) true) <-> (is_value_of_expr e).
Proof.
 intros.
 split.
 (* xis -> is*)
  intros.
  induction e.
  (* ident *)
   simpl in H.
   apply diff_true_false.
   symmetry.
   trivial.
  (* constant *)
   simpl.
   trivial.
  (* apply *)
   simpl in H.
   simpl.
   apply diff_true_false.
   symmetry.
   trivial.
  (* bind *) 
   simpl.
   trivial.
   simpl in H.
   apply diff_true_false.
   symmetry.
   trivial.
  (* function *) 
   simpl; trivial.
  (* live *)
   simpl; trivial.
  (* pair *)
   simpl in H.
   simpl.
   split.
   destruct (xis_value_of_expr e1).
   auto.
   auto.
   destruct (xis_value_of_expr e2).
   auto.
   destruct (xis_value_of_expr e1).
   auto.
   auto.
  (* tagging left *)
   simpl.
   auto.
  (* tagging right *) 
   simpl.
   auto.
  (* case *) 
   simpl in H.
   simpl.
   apply diff_true_false.
   symmetry.
   trivial.
 (* is -> xis *)
  intros.
  induction e.
  (* ident *) 
   simpl in H.
   contradiction.
  (* constant *)
   simpl; trivial.
  (* apply *)
   simpl in H; contradiction.
  (* bind *)
   simpl in H; contradiction.
  (* function *)
   simpl; trivial.
  (* live *)
   simpl; trivial.
  (* pair *)
   simpl in H.
   decompose [and] H. 
   simpl in IHe1.
   simpl.
   rewrite IHe1.
   auto.
   auto.
  (* tagging left *)
   simpl; simpl in H; auto.
  (* tagging right *)
   simpl; simpl in H; auto.
  (* case *)
   simpl; contradiction.
Qed.

Fixpoint yval (e : expr) (b : bool) : Prop := (eq (xis_value_of_expr e) b).



(* defns Jop *)
Inductive XJO_red : expr -> expr -> Prop :=    (* defn red *)
 | XJO_red_app : forall (x:value_name) (t : typexpr) (e v:expr),
     (eq (xis_value_of_expr v) true) ->
     XJO_red (E_apply  (E_function x t e)  v)  (subst_expr  v   x   e ) 
 | XJO_red_forkmove1 : forall (e e' e'':expr),
     (eq (xis_value_of_expr e) false) ->
     (eq (xis_value_of_expr e') false) ->
     (eq select First) ->    
     XJO_red e e'' ->
     XJO_red (E_apply  (E_apply (E_constant CONST_fork)  (E_live_expr e) )   (E_live_expr e') ) (E_apply  (E_apply (E_constant CONST_fork)  (E_live_expr e'') )   (E_live_expr e') )
 | XJO_red_forkmove2 : forall (e e' e'':expr),
     (eq (xis_value_of_expr e) false) ->
     (eq (xis_value_of_expr e') false) -> 
     (eq select Second) ->
     XJO_red e' e'' ->
     XJO_red (E_apply  (E_apply (E_constant CONST_fork)  (E_live_expr e) )   (E_live_expr e') ) (E_apply  (E_apply (E_constant CONST_fork)  (E_live_expr e) )   (E_live_expr e'') )
(* | XJO_red_forkmove12 : forall (e e' e'' e''':expr),
     (eq select Both) ->
     (eq (xis_value_of_expr e) false) ->
     (eq (xis_value_of_expr e') false) ->
     XJO_red e e'' ->
     XJO_red e' e''' ->
     XJO_red (E_apply  (E_apply (E_constant CONST_fork)  (E_live_expr e) )   (E_live_expr e') ) (E_apply  (E_apply (E_constant CONST_fork)  (E_live_expr e'') )   (E_live_expr e''') )
*) | XJO_red_forkdeath1 : forall (v e':expr),
     (eq (xis_value_of_expr v) true) ->
     (eq (xis_value_of_expr e') false) ->
     XJO_red (E_apply  (E_apply (E_constant CONST_fork)  (E_live_expr v) )   (E_live_expr e') ) (E_live_expr (E_pair v  (E_live_expr e') ))
 | XJO_red_forkdeath2 : forall (v e:expr),
     (eq (xis_value_of_expr v) true) ->
     (eq (xis_value_of_expr e) false) ->
     XJO_red (E_apply  (E_apply (E_constant CONST_fork)  (E_live_expr e) )   (E_live_expr v) ) (E_live_expr (E_pair  (E_live_expr e)  v))
 | XJO_red_forkdeath12 : forall (v v':expr),
     (eq (xis_value_of_expr v) true) ->
     (eq (xis_value_of_expr v') true)->
     XJO_red (E_apply  (E_apply (E_constant CONST_fork)  (E_live_expr v) )   (E_live_expr v') ) (E_live_expr (E_pair v v'))
 | XJO_red_ret : forall (v:expr),
     (eq (xis_value_of_expr v) true) ->
     XJO_red (E_apply (E_constant CONST_ret) v) (E_live_expr v)
 | XJO_red_evalbind : forall (e e'' e':expr),
     XJO_red e e' ->
     XJO_red (E_bind e e'') (E_bind e' e'')
 | XJO_red_movebind : forall (e e'' e':expr),
     (eq (xis_value_of_expr e) false) -> 
     XJO_red e e' ->
     XJO_red (E_bind  (E_live_expr e)  e'') (E_bind  (E_live_expr e')  e'')
 | XJO_red_dobind : forall (v e:expr),
     (eq (xis_value_of_expr v) true) ->
     XJO_red (E_bind  (E_live_expr v)  e) (E_apply e v)
 | XJO_red_context_app1 : forall (e e' e'':expr),
     (eq (xis_value_of_expr e') false) ->
     XJO_red e' e'' ->
     XJO_red (E_apply e e') (E_apply e e'')
 | XJO_red_context_app2 : forall (e v e':expr),
     (eq (xis_value_of_expr v) true) ->
     XJO_red e e' ->
     XJO_red (E_apply e v) (E_apply e' v)
 | XJO_red_pair_1 : forall (e e'' e':expr),
     (eq (xis_value_of_expr e) false) ->
     XJO_red e e' ->
     XJO_red (E_pair e e'') (E_pair e' e'')
 | XJO_red_pair_2 : forall (v e e':expr),
     (eq (xis_value_of_expr v) true) ->
     XJO_red e e' ->
     XJO_red (E_pair v e) (E_pair v e')
 | XJO_red_evalinl : forall (e e':expr),
     XJO_red e e' ->
     XJO_red (E_taggingleft e) (E_taggingleft e')
 | XJO_red_evalinr : forall (e e':expr),
     XJO_red e e' ->
     XJO_red (E_taggingright e) (E_taggingright e')
 | XJO_red_evalcaseinl : forall (x:value_name) (e:expr) (x':value_name) (e' v:expr),
     (eq (xis_value_of_expr v) true) ->
     XJO_red (E_case  (E_taggingleft v)  x e x' e')  (subst_expr  v   x   e ) 
 | XJO_red_evalcaseinr : forall (x:value_name) (e:expr) (x':value_name) (e' v:expr),
     (eq (xis_value_of_expr v) true) ->
     XJO_red (E_case  (E_taggingright v)  x e x' e')  (subst_expr  v   x'   e' ) 
 | XJO_red_evalcase : forall (e:expr) (x:value_name) (e'':expr) (x':value_name) (e''' e':expr),
     (eq (xis_value_of_expr e) false) ->
     XJO_red e e' ->
     XJO_red (E_case e x e'' x' e''') (E_case e' x e'' x' e''').  

Lemma red_not_value : forall (e e' : expr), (XJO_red e e') -> (eq (xis_value_of_expr e) false).
Proof.
Admitted.

Theorem red_is_xred : forall (e e' : expr), JO_red e e' <-> XJO_red e e'.
Proof.
Admitted. 

(*Extraction Relation Fixpoint is_expr_of_expr [1]. *)

Recursive Extraction xis_value_of_expr.

Extraction Relation Relaxed XJO_red [1].