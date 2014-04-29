Require Import Arith.
Require Import Bool.
Require Import Sumbool.
Require Import List.
Require Import Classical_Prop.


Load mconextract.


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
   induction e1.
   inversion H.
   case_eq constant5.
   intros.
   rewrite -> H0 in H.
   inversion H.
   intros.
   rewrite -> H0 in H.
   rewrite -> H0 in IHe1.
   simpl.
   apply IHe2.
   inversion H.
   reflexivity.
   intros.
   rewrite -> H0 in H.
   inversion H.
   simpl in H.
   intros.
   rewrite -> H0 in H.
   apply diff_true_false.
   symmetry;trivial.
   intros; simpl; auto.
   apply IHe2.
   simpl in H; trivial.
   intuition.
   inversion H1.
   rewrite H0 in H.
   trivial.
   intuition.
   rewrite H0 in H.
   inversion H.
   intros; rewrite H0 in H; inversion H.
   inversion H.
   auto.
   inversion H.
   simpl.
   simpl in H.
   congruence.
   inversion H.
   inversion H.
   inversion H.
   inversion H.
   inversion H.
   inversion H.
  (* bind *) 
   simpl.
   trivial.
   simpl; trivial.
   simpl in H.
   intuition. 
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
   induction e1.
   simpl in H.
   elim H.
   simpl in H.
   case_eq constant5.
   intros.
   rewrite -> H0 in H.
   elim H.
   intros.
   rewrite -> H0 in H.
   simpl.
   apply IHe2.
   trivial.
   intros.
   rewrite -> H0 in H.
   auto.
   intros; rewrite H0 in H; auto.
   intros; simpl.
   rewrite H0 in H; apply IHe2; trivial.
   intro H0; rewrite H0 in H; auto.
   intro H0; rewrite H0 in H; auto.
   simpl in H.
   auto.
   simpl in H.
   auto.
   simpl; auto.
   simpl; auto.
   simpl; auto.
   simpl; auto.
   simpl; auto.
   simpl; auto.
   simpl; auto.
  (* bind *)
   simpl in H; contradiction.
  (* function *)
   simpl; trivial.
  (* fix *)
  simpl in H. intuition.
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



Hint Resolve eq_value_name : ott_coq_equality.
(*
Lemma eq_typscheme: forall (x y : typscheme), {x = y} + {x <> y}.
Proof.
decide equality. decide equality. apply eq_typvar. decide equality. apply eq_typvar.
Qed.
Hint Resolve eq_typscheme : ott_coq_equality.

(* Extractable VTSin *)

Fixpoint XVTSin (v : value_name) (ts : typscheme)  (G5 : G) : bool := 
 match G5 with 
 | G_em => false 
 | G_vn (G6 ) (v' ) (ts' ) => if (eq_value_name v v') then ( if (eq_typscheme ts ts') then true else false) else XVTSin v ts G6
end.

(* Proof that the extractable VTSin is the same as the original *)

Lemma xvtsin_eq_vtsin : forall (v : value_name) (ts : typscheme)  (G5 : G), XVTSin v ts G5 = true <-> VTSin v ts G5.
Proof.
 intros.
 split.
 intros.
 induction G5.
 simpl in H.
 symmetry in H.
 apply diff_true_false in H.
 contradiction.
 destruct (eq_value_name v value_name5).
 rewrite <- e.
 destruct (eq_typscheme ts typscheme5).
 rewrite <- e0.
 apply VTSin_vn1.
 apply VTSin_vn2.
 apply IHG5.
 rewrite <- e in H.
 simpl in H.
 destruct (eq_value_name v v).
 destruct (eq_typscheme ts typscheme5).
 contradiction.
 symmetry in H.
 apply diff_true_false in H.
 contradiction.
 trivial.
 rewrite <- e in H.
 simpl in H.
 destruct (eq_value_name v v).
 destruct (eq_typscheme ts typscheme5).
 contradiction.
 symmetry in H.
 apply diff_true_false in H.
 contradiction.
 trivial.
 simpl in H.
 destruct (eq_value_name v value_name5).
 contradiction.
 apply VTSin_vn2.
 apply IHG5.
 trivial.
 trivial.
 intros.
 induction G5.
 inversion H.
 simpl.
 destruct (eq_value_name v value_name5).
 rewrite <- e in H.
 destruct (eq_typscheme ts typscheme5).
 trivial.
 inversion H.
 rewrite -> H4 in n.
 cut (typscheme5 = typscheme5).
 intros.
 contradiction.
 auto.
 cut (v = v).
 intros.
 contradiction.
 auto.
 inversion H.
 contradiction.
 apply IHG5.
 trivial.
Qed.

Fixpoint GetTS (v : value_name)  (G5 : G)  : option typscheme :=
match G5 with 
 | G_em => None 
 | G_vn (G6 ) (v' ) (ts' ) => if (eq_value_name v v') then ( Some ts') else GetTS v G6
end.

Lemma eq_typexpr: forall (x y : typexpr), {x = y} + {x <> y}.
Proof.
decide equality. apply eq_typvar. 
Qed.
Hint Resolve eq_typexpr : ott_coq_equality.

Fixpoint newTV0 (l : list_typvar) (s : nat) : typvar :=
 match l with 
 | Nil_list_typvar => TV_ident(s)
 | Cons_list_typvar (TV_ident (n)) l' => newTV0 l' (s+n+1)
end.

Fixpoint newTV (l : list_typvar) : typvar := 
 let newTV0 (lt : list_typvar) (s : nat) : typvar :=
 match l with 
 | Nil_list_typvar => TV_ident(s)
 | Cons_list_typvar (TV_ident (n)) lt' => newTV0 lt' (s+n+1)
 end in
 newTV0 l 0.

Fixpoint generalise (G5 : G) (T : typexpr) : typscheme := (TS_ts (remove_duplicates (make_list_typvar (list_minus eq_typvar (ftv_typexpr T) (ftv_G G5)))) T).

Fixpoint occurs (v : typvar) (e : typexpr) : bool :=
 match e with
 | TE_var (typvar5 ) => if eq_typvar v typvar5 then true else false
 | TE_arrow (typexpr5) (typexpr') => orb (occurs v typexpr5) (occurs v typexpr')
 | TE_prod (typexpr5) (typexpr') => orb (occurs v typexpr5) (occurs v typexpr')
 | TE_concurrent (typexpr5) => occurs v typexpr5
 | TE_sum (typexpr5) (typexpr') => orb (occurs v typexpr5) (occurs v typexpr')
end.

Fixpoint mgu (e1 : typexpr) (e2 : typexpr)  : option (list (typvar*typexpr))  :=
 match e1 with 
 | TE_var (typvar5 ) => if (occurs typvar5 e2) 
                         then match e2 with 
                              | TE_var (typvar6 ) => Some (cons (pair typvar5 e2) nil)
                              | _ => None
                              end
                         else Some (cons (pair typvar5 e2) nil)
 | TE_arrow (typexpr5) (typexpr') => 
    match e2 with 
    | TE_var (typvar5 ) => if (occurs typvar5 e1) then None else Some (cons (pair typvar5 e1) nil)
    | TE_arrow (typexpr6) (typexpr'') => match mgu typexpr5 typexpr6 with
                                         | None => None
                                         | Some l => match mgu (tsubst_typexpr l typexpr') typexpr'' with
                                                     | None => None
                                                     | Some l' => Some (app l l') 
                                                     end
                                         end
    | _ => None
    end
 | TE_prod (typexpr5) (typexpr') => 
     match e2 with 
    | TE_var (typvar5 ) => if (occurs typvar5 e1) then None else Some (cons (pair typvar5 e1) nil)
    | TE_prod (typexpr6) (typexpr'') => match mgu typexpr5 typexpr6 with
                                         | None => None
                                         | Some l => match mgu (tsubst_typexpr l typexpr') typexpr'' with
                                                     | None => None
                                                     | Some l' => Some (app l l')
                                                     end
                                         end
    | _ => None
    end
 | TE_concurrent (typexpr5) => 
    match e2 with 
    | TE_var (typvar5 ) => if (occurs typvar5 e1) then None else Some (cons (pair typvar5 e1) nil)
    | TE_concurrent (typexpr6) => mgu typexpr5 typexpr6
    | _ => None
    end
 | TE_sum (typexpr5) (typexpr') => 
    match e2 with 
    | TE_var (typvar5 ) => if (occurs typvar5 e1) then None else Some (cons (pair typvar5 e1) nil)
    | TE_sum (typexpr6) (typexpr'') => match mgu typexpr5 typexpr6 with
                                         | None => None
                                         | Some l => match mgu (tsubst_typexpr l typexpr') typexpr'' with
                                                     | None => None
                                                     | Some l' => Some (app l l')
                                                     end
                                         end
    | _ => None
    end
end.

Lemma empty_sub : forall (tv : typvar) (texp0 texp : typexpr), (occurs tv texp = false) ->  (tsubst_typexpr ((pair tv texp0)::nil) texp) = texp.
Proof. 
 intros.
 induction texp.
 simpl.
 simpl in H.
 destruct (eq_typvar tv typvar5).
 congruence.
 reflexivity.
 simpl in H.
 case_eq (occurs tv texp1).
 intros.
 rewrite -> H0 in H.
 simpl in H.
 congruence.
 intros. case_eq (occurs tv texp2). intros. 
 rewrite -> H1 in H. rewrite -> H0 in H. simpl in H. congruence. 
 intros.
 assert (tsubst_typexpr ((tv, texp0) :: nil) texp1 = texp1).
 apply IHtexp1.
 trivial.
 assert (tsubst_typexpr ((tv, texp0) :: nil) texp2 = texp2).
 apply IHtexp2.
 trivial.
 simpl.
 rewrite -> H2.
 rewrite -> H3.
 reflexivity.
 simpl in H.
 case_eq (occurs tv texp1).
 intros.
 rewrite -> H0 in H.
 simpl in H.
 congruence.
 intros. case_eq (occurs tv texp2). intros. 
 rewrite -> H1 in H. rewrite -> H0 in H. simpl in H. congruence. 
 intros.
 assert (tsubst_typexpr ((tv, texp0) :: nil) texp1 = texp1).
 apply IHtexp1.
 trivial.
 assert (tsubst_typexpr ((tv, texp0) :: nil) texp2 = texp2).
 apply IHtexp2.
 trivial.
 simpl.
 rewrite -> H2.
 rewrite -> H3.
 reflexivity.
 simpl in H.
 assert (tsubst_typexpr ((tv, texp0) :: nil) texp = texp).
 apply IHtexp.
 trivial.
 simpl.
 rewrite -> H0.
 reflexivity.
 simpl in H.
 case_eq (occurs tv texp1).
 intros.
 rewrite -> H0 in H.
 simpl in H.
 congruence.
 intros. case_eq (occurs tv texp2). intros. 
 rewrite -> H1 in H. rewrite -> H0 in H. simpl in H. congruence. 
 intros.
 assert (tsubst_typexpr ((tv, texp0) :: nil) texp1 = texp1).
 apply IHtexp1.
 trivial.
 assert (tsubst_typexpr ((tv, texp0) :: nil) texp2 = texp2).
 apply IHtexp2.
 trivial.
 simpl.
 rewrite -> H2.
 rewrite -> H3.
 reflexivity.
Qed.


Theorem mgu_unifies : forall (e1 e2 : typexpr) (l : list (typvar*typexpr)), (mgu e1 e2 = Some l -> ((tsubst_typexpr l e1)=(tsubst_typexpr l e2))).
Proof.
 intro e1.
 intro e2.
 induction e1; induction e2.
(* var - var *)
 intros.
 simpl in H.
 destruct (eq_typvar typvar5 typvar0).
 cut ((typvar5, TE_var typvar0) :: nil = l).
 intros.
 rewrite <- H0.
 simpl.
 destruct (eq_typvar typvar5 typvar5).
 destruct (eq_typvar typvar5 typvar0).
 reflexivity.
 reflexivity.
 assert (typvar5 = typvar5).
 reflexivity.
 contradiction.
 simpl in H.
 congruence.
 assert  ((typvar5, TE_var typvar0) :: nil = l).
 congruence.
 rewrite <- H0.
 simpl.
 destruct (eq_typvar typvar5 typvar5).
 destruct (eq_typvar typvar5 typvar0).
 reflexivity.
 reflexivity.
 destruct (eq_typvar typvar5 typvar0).
 contradiction.
 assert (typvar5 = typvar5).
 reflexivity.
 contradiction.
(* var - arrow*)
 intros.
 simpl in H.
 case_eq (occurs typvar5 e2_1).
 intros.
 rewrite -> H0 in H.
 simpl in H.
 congruence.
 intros.
 rewrite -> H0 in H.
 simpl in H.
 case_eq (occurs typvar5 e2_2).
 intros.
 rewrite -> H1 in H.
 simpl in H.
 congruence.
 intros.
 rewrite -> H1 in H.
 simpl in H.
 assert (((typvar5, TE_arrow e2_1 e2_2) :: nil) = l).
 congruence.
 auto.
 assert ((occurs typvar5 (TE_arrow e2_1 e2_2)) = false).
 simpl.
 rewrite -> H0.
 rewrite -> H1.
 auto.
 rewrite <- H2.
 assert ((tsubst_typexpr ((typvar5, TE_arrow e2_1 e2_2) :: nil) (TE_arrow e2_1 e2_2)) = (TE_arrow e2_1 e2_2)).
 apply empty_sub.
 trivial.
 rewrite -> H4.
 simpl.
 destruct (eq_typvar typvar5 typvar5).
 reflexivity.
 congruence.
(* var - prod *)
 intros. 
 simpl in H.
 case_eq (occurs typvar5 e2_1).
 intros.
 rewrite -> H0 in H.
 simpl in H.
 congruence.
 intros.
 rewrite -> H0 in H.
 simpl in H.
 case_eq (occurs typvar5 e2_2).
 intros.
 rewrite -> H1 in H.
 simpl in H.
 congruence.
 intros.
 rewrite -> H1 in H.
 simpl in H.
 assert (((typvar5, TE_prod e2_1 e2_2) :: nil) = l).
 congruence.
 auto.
 assert ((occurs typvar5 (TE_prod e2_1 e2_2)) = false).
 simpl.
 rewrite -> H0.
 rewrite -> H1.
 auto.
 rewrite <- H2.
 assert ((tsubst_typexpr ((typvar5, TE_prod e2_1 e2_2) :: nil) (TE_prod e2_1 e2_2)) = (TE_prod e2_1 e2_2)).
 apply empty_sub.
 trivial.
 rewrite -> H4.
 simpl.
 destruct (eq_typvar typvar5 typvar5).
 reflexivity.
 congruence.
(* var - concurrent *)
 intros.
 simpl in H.
 case_eq (occurs typvar5 e2).
 intros.
 rewrite -> H0 in H.
 congruence.
 intros.
 rewrite -> H0 in H.
 assert (((typvar5, TE_concurrent e2) :: nil) = l).
 congruence.
 rewrite <- H1.
 assert ((tsubst_typexpr ((typvar5, TE_concurrent e2) :: nil) (TE_concurrent e2)) = (TE_concurrent e2)).
 apply empty_sub.
 simpl.
 trivial.
 rewrite -> H2.
 simpl.
 destruct (eq_typvar typvar5 typvar5).
 reflexivity.
 congruence.
(* var - sum *)
 intros.
 simpl in H.
 case_eq (occurs typvar5 e2_1).
 intros.
 rewrite -> H0 in H.
 simpl in H.
 congruence.
 intros.
 rewrite -> H0 in H.
 simpl in H.
 case_eq (occurs typvar5 e2_2).
 intros.
 rewrite -> H1 in H.
 simpl in H.
 congruence.
 intros.
 rewrite -> H1 in H.
 simpl in H.
 assert (((typvar5, TE_sum e2_1 e2_2) :: nil) = l).
 congruence.
 auto.
 assert ((occurs typvar5 (TE_sum e2_1 e2_2)) = false).
 simpl.
 rewrite -> H0.
 rewrite -> H1.
 auto.
 rewrite <- H2.
 assert ((tsubst_typexpr ((typvar5, TE_sum e2_1 e2_2) :: nil) (TE_sum e2_1 e2_2)) = (TE_sum e2_1 e2_2)).
 apply empty_sub.
 trivial.
 rewrite -> H4.
 simpl.
 destruct (eq_typvar typvar5 typvar5).
 reflexivity.
 congruence.
(* arrow *)
 simpl.
 intro l0.
 intros.
 simpl in H.
(* arrow - var *)
 simpl in H.
 case_eq (occurs typvar5 e1_1).
 intros.
 rewrite -> H0 in H.
 simpl in H.
 congruence.
 intros.
 rewrite -> H0 in H.
 case_eq (occurs typvar5 e1_2).
 intros.
 rewrite -> H1 in H.
 simpl in H.
 congruence.
 intros.
 rewrite -> H1 in H.
 simpl in H.
 assert (((typvar5, TE_arrow e1_1 e1_2) :: nil) = l0).
 congruence.
 rewrite <- H2.
 assert ((tsubst_typexpr ((typvar5, TE_arrow e1_1 e1_2) :: nil) e1_1) = (e1_1)).
 apply empty_sub.
 trivial.
 assert ((tsubst_typexpr ((typvar5, TE_arrow e1_1 e1_2) :: nil) e1_2) = (e1_2)).
 apply empty_sub.
 trivial.
 rewrite -> H3.
 rewrite -> H4.
 simpl.
 destruct (eq_typvar typvar5 typvar5).
 reflexivity.
 congruence.
(* arrow - arrow *)
 intro l0.
 intros.
 simpl in H.
 case_eq (mgu e1_1 e2_1).
 intro l.
 intro.
 rewrite -> H0 in H.
 simpl H.
 case_eq (mgu (tsubst_typexpr l e1_2) e2_2).
 intro l'.
 intros.
 rewrite -> H1 in H.
 assert ((l ++ l') = l0).
 congruence.
 simpl.
 constructor 2.
 simpl.
(* assert (tsubst_typexpr l e1_1 = tsubst_typexpr l (TE_arrow e2_1 e2_2)).
 apply IHe1_1.
 simpl in H. *)
Qed.




Inductive constraint : Set := 
 | constr (s : typexpr) (t : typexpr).

Fixpoint TypeCheckConstr (G5 : G) (e : expr) (T: typexpr) (X : list_typvar) (constrs : list constraint) : bool :=
  match e with 
  | (E_ident x) => false
  | (E_function (value_name5:value_name) (typexpr5:typexpr) (expr5:expr)) => 
       match T with
       | TE_arrow (typexpr6:typexpr) (typexpr7:typexpr) => if (eq_typexpr typexpr5 typexpr6) 
                                                           then TypeCheckConstr (G_vn G5 (value_name5) (generalise G5 typexpr5)) expr5 typexpr7 X constrs 
                                                           else false                                                                 
       | _ => false
       end
  | E_apply (e1:expr) (e2:expr) =>  


Fixpoint InferType (G5 : G) (e : expr) : option typscheme :=
 let infT (G5 : G) (e : expr) (usedTV : list_typvar) : option typscheme :=
 match e with 
 | (E_ident x) => match GetTS x G5 with 
                   | Some ts => Some ts
                   | None => let ntv := newTV usedTV in Some (TS_ts (Cons_list_typvar (ntv) Nil_list_typvar) (TE_var (ntv)))
                  end
 | (E_apply e' e'') => let ts1 := InferType G5 e' in
                       let ts2 := InferType G5 e'' in 
                        match ts1 with 
                        | Some (TS_ts tvs texp) =>
                           match texp with 
                           | TE_arrow texparg texpret => None
                           | _ => None
                           end
                        | _ => None
                        end
  | _ => None                                     
end
in infT (G5 : G) (e : expr) Nil_list_typvar.

Fixpoint Typecheck (G5 : G) (e : expr) (t : typexpr) : bool :=
 match e with 
  | E_constant CONST_ret => match t with | (TE_arrow t' (TE_concurrent t'')) =>  if eq_typexpr t' t'' then true else false | _ => false end
  | E_constant CONST_fork => match t with 
                             | (TE_arrow  (TE_concurrent t1)   (TE_arrow  (TE_concurrent t2)   (TE_concurrent  (TE_sum  (TE_sum  (TE_prod t1' t2')   (TE_prod t1''  (TE_concurrent t2'') ) )   (TE_prod  (TE_concurrent t1''')  t2''') ) ) ) )
                               => if eq_typexpr t1 t1' then if eq_typexpr t1' t1'' then if eq_typexpr t1'' t1''' then if eq_typexpr t2 t2' then if eq_typexpr t2' t2'' then if eq_typexpr t2'' t2''' then true else false else false else false else false else false else false
                             | _ => false
                             end
  | E_apply e' e'' => match t with | TE_arrow t' t'' => andb (Typecheck G5 e' t') (Typecheck G5 e'' t'') | _ => false end
  | E_function x1 t1 e1 => match t with | (TE_arrow t1 t2) => Typecheck (G_vn G5 x1 (TS_ts Nil_list_typvar t1)) e1 t2 | _ => false end
  | E_live_expr e1 => match t with | (TE_concurrent t1) => Typecheck G5 e1 t1 | _ => false end
  | E_bind e1 e2 => false
  | _ => false
 end. 
*)



 
(*
Lemma not_value_red : forall (e : expr), (~(is_value_of_expr e) /\ (exists (t : typexpr), Get G_em e t)) -> (exists (e' : expr), (JO_red e e')).
Proof.
 intro e.
 induction e.
 intros.
 simpl in H.
 elim H.
 intros.
 elim H1.
 intros.
 inversion H2.
 assert (~ (VTSin value_name5 typscheme5 G_em)).
 apply empty_VTSin_false.
 contradiction.
 intros.
 elim H.
 intros.
 assert (is_value_of_expr (E_constant constant5)).
 simpl.
 trivial.
 contradiction.
 intros.
 elim H.
 intros.
 elim H1.
 intros.
 inversion H2.
 assert ((is_value_of_expr e2) \/ (~(is_value_of_expr e2))).
 apply is_value_of_expr_dec.
 elim H9.
 intros.
 inversion H6.
 assert (~(VTSin x0 typscheme5 G_em)).
 apply empty_VTSin_false.
 contradiction.
 inversion H11.
 exists ((E_live_expr e2)).
 apply JO_red_ret.
 trivial.
 rewrite <- H13 in H0.
 rewrite <- H16 in H0.
 simpl in H0.
 contradiction.
 inversion H11.
 apply empty_VTSin_false in H16.
 elim H16.
 inversion H16.
 rewrite <- H23 in H12. 
 rewrite <- H24 in H8.
 assert ((exists e2' : expr, JO_red e2 e2') \/ ~ (exists e2' : expr, JO_red e2 e2')).
 apply classic with (P :=  (exists e2' : expr, JO_red e2 e2')).
 elim H22.
 intros.
 elim H26.
 intros.
 assert (JO_red (E_apply (E_apply (E_constant CONST_fork) e'0) e2) (E_apply (E_apply (E_constant CONST_fork) e'0) x0)).
 apply JO_red_context_app1.
 trivial.
 exists ((E_apply (E_apply (E_constant CONST_fork) e'0) x0)).
 trivial.
 intros.
 assert ((exists y : expr, JO_red e'0 y) \/ ~ (exists y : expr, JO_red e'0 y)).
 apply classic with (P :=  (exists y : expr, JO_red e'0 y)).
 elim H27.
 intros.
 elim H28.
 intros.
 assert (JO_red  (E_apply (E_constant CONST_fork) e'0) (E_apply (E_constant CONST_fork) x0)).
 apply JO_red_context_app1.
 trivial.
 assert (JO_red (E_apply (E_apply (E_constant CONST_fork) e'0) e2) (E_apply (E_apply (E_constant CONST_fork) x0) e2)).
 apply JO_red_context_app2.
 assert ((is_value_of_expr e2) \/ ~(is_value_of_expr e2)).
 apply classic.
 elim H31.
 intros; trivial.
 intros.
 assert (exists e' : expr, JO_red e2 e').
 apply IHe2.
 split.
 trivial.
 exists ((TE_concurrent t5)).
 trivial.
 unfold not in H26.
 auto.
 trivial.
 exists ((E_apply (E_apply (E_constant CONST_fork) x0) e2)).
 trivial.
 intros.
 assert ((is_value_of_expr e2) \/ ~(is_value_of_expr e2)).
 apply classic.
 elim H29.
 intros.
 induction e2.
 simpl in H30.
 elim H30.
 induction constant0.
 inversion H8.
 inversion H33.
 inversion H8.
 inversion H33. 
 simpl in H30.
 inversion H8.
 inversion H33.
 (*apply JO_red_forkdeath12 with (.
 simpl in H30.
 induction e2_1.
 elim H30.
 induction constant0.
 elim H30.
 in *)
Qed.
(*  
 simpl.
 
 induction e2_1.
 simpl in H30; elim H30.
 simpl in H30.
 induction constant0.
 simpl in H30; elim H30.
 

 rewrite <- H14 in H2.
 simpl in H2.

 exists ((E_apply (E_apply (E_constant CONST_fork) e'0) x0)).
 trivial.
 intros. 


 auto.

 inversion H8.
 apply empty_VTSin_false in H22.
 elim H22.
 assert 
 inversion H22.
 simpl in H22.
 
 case (is_value_of_expr e2).
 simpl.
 simpl H2. 

 auto.
 simpl.
 simpl. 


 inversion H4.
 intros.
 elim H.
 intros.
 simpl in H0.
 assert False.
 unfold not in H0.
 apply H0.
 trivial.
 absurd (False).
 unfold not.
 intros. 
 trivial.
 trivial.
 intros.
 elim H.
 intros.
 elim H1.
 intros.
 inversion H2.
 inversion H6.
 rewrite <- H12 in H6.
 inversion H6.
 inversion JO_red.
 simpl.
 simpl H2.
 case_eq H4.
 intros.
 inversion in H4.
 simpl in H4.
 simpl in H.
 simpl.
Qed.
 *)

(* Proof that reduction and the extractable reduction is equivalent *)
 (*Theorem xred_if_red : forall (e e' : expr), JO_red e e' -> (exists (s : selectSet), (XJO_red e e')).
Proof.
 intros.
 inversion H.
 exists First.
 apply XJO_red_app.
 apply l_val.
 trivial.
 exists First.
 apply XJO_red_forkmove1.
 apply red_not_value in H.
 apply not_true_is_false.
 apply red_not_value in H0.
 rewrite <- l_val in H0.
 trivial.
 apply First.
 apply First.
 apply red_not_value in H0.
 rewrite <- l_val in H0.
 apply not_true_is_false.
 trivial.
 trivial.
Qed.*) 
(*
Theorem red_if_xred : forall (e e' : expr), XJO_red e e' -> (JO_red e e').
Proof.
 intro e.
 induction e.
 intros.
 inversion H.
 intros.
 inversion H.
 intros.
 inversion H.
 apply JO_red_app.
 apply l_val in H3. 
 trivial.
 apply JO_red_forkmove1.
 induction e1.
 congruence.
 congruence.
 simpl in H0.
 induction e1_2.
 congruence.
 congruence.
 congruence.
 congruence.
 congruence.
 assert (e1_1 = (E_constant CONST_fork)).
 congruence.
 assert (e = e1_2).
 congruence.
 rewrite <- H8 in H.
 rewrite <- H8 in IHe1_2.
 rewrite <- H8 in IHe1_0.
 rewrite -> H7 in H.
 rewrite -> H7 in IHe1_1.
 rewrite -> H7 in IHe1_0.
 apply IHe1_0.
 rewrite <- H8 in IHe1.
 rewrite -> H7 in IHe1.
 trivial.
 congruence.
 intros.
 inversion H.
 apply JO_red_app.
 apply l_val in H0.
 trivial.
 induction e.
 apply JO_red_forkmove1.
 simpl.
Qed.
*)
