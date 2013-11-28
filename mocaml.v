(* generated by Ott 0.23 from: ./mocaml.ott *)

Require Import Arith.
Require Import Bool.
Require Import List.


Definition value_name := nat.
Lemma eq_value_name: forall (x y : value_name), {x = y} + {x <> y}.
Proof.
  decide equality; auto with ott_coq_equality arith.
Defined.
Hint Resolve eq_value_name : ott_coq_equality.
Definition ident := nat.
Definition integer_literal := nat.
Definition index := nat.

Inductive typvar : Set := 
 | TV_ident (ident5:ident).

Inductive typeconstr : Set := 
 | TC_unit : typeconstr
 | TC_bool : typeconstr
 | TC_int : typeconstr.

Inductive constant : Set := 
 | CONST_int (integer_literal5:integer_literal)
 | CONST_false : constant
 | CONST_true : constant
 | CONST_unit : constant
 | CONST_and : constant
 | CONST_not : constant
 | CONST_ret : constant
 | CONST_fork : constant.

Inductive typexpr : Set := 
 | TE_var (typvar5:typvar)
 | TE_arrow (typexpr5:typexpr) (typexpr':typexpr)
 | TE_constr0 (typeconstr5:typeconstr)
 | TE_prod (typexpr5:typexpr) (typexpr':typexpr)
 | TE_concurrent (typexpr5:typexpr)
 | TE_sum (typexpr5:typexpr) (typexpr':typexpr).

Inductive list_typvar : Set := 
 | Nil_list_typvar : list_typvar
 | Cons_list_typvar (_:typvar) (_:list_typvar).

Inductive expr : Set := 
 | E_ident (value_name5:value_name)
 | E_constant (constant5:constant)
 | E_apply (expr5:expr) (expr':expr)
 | E_bind (expr5:expr) (expr':expr)
 | E_function (value_name5:value_name) (expr5:expr)
 | E_let (value_name5:value_name) (expr5:expr) (expr':expr)
 | E_live_expr (expr5:expr)
 | E_dead_expr (value5:expr)
 | E_pair (e:expr) (e':expr)
 | E_taggingleft (e:expr)
 | E_taggingright (e:expr)
 | E_case (e1:expr) (x1:value_name) (e2:expr) (x2:value_name) (e3:expr).

Inductive typscheme : Set := 
 | TS_ts (_:list_typvar) (typexpr5:typexpr).

Inductive G : Set := 
 | G_em : G
 | G_vn (G5:G) (value_name5:value_name) (typscheme5:typscheme).
Lemma eq_typvar: forall (x y : typvar), {x = y} + {x <> y}.
Proof.
decide equality. apply eq_value_name.
Defined.
Hint Resolve eq_typvar : ott_coq_equality.
Fixpoint map_list_typvar (A:Set) (f:typvar->A) (l:list_typvar) : list A :=
  match l with
  | Nil_list_typvar => nil
  | Cons_list_typvar h tl_ => cons (f h) (map_list_typvar A f tl_)
  end.
Implicit Arguments map_list_typvar.

Fixpoint make_list_typvar (l: list typvar): list_typvar :=
  match l with
  | nil  => Nil_list_typvar
  | cons h tl_ => Cons_list_typvar h (make_list_typvar tl_)
  end.

Fixpoint unmake_list_typvar (l: list_typvar): list typvar :=
  match l with
  | Nil_list_typvar => nil
  | Cons_list_typvar h tl_ => cons h (unmake_list_typvar tl_)
  end.

Fixpoint nth_list_typvar (n:nat) (l: list_typvar) {struct n} : option typvar :=
  match n,l with
  | O, Cons_list_typvar h tl_ => Some h
  | O, _ => None
  | S m, Nil_list_typvar => None
  | S m, Cons_list_typvar h tl_ => nth_list_typvar m tl_
  end.

Fixpoint app_list_typvar (l m: list_typvar): list_typvar :=
  match l with
  | Nil_list_typvar => m
  | Cons_list_typvar h tl_ => Cons_list_typvar h (app_list_typvar tl_ m)
  end.



(** subrules *)
Fixpoint is_expr_of_expr (e_5:expr) : Prop :=
  match e_5 with
  | (E_ident value_name5) => (True)
  | (E_constant constant5) => (True)
  | (E_apply expr5 expr') => ((is_expr_of_expr expr5) /\ (is_expr_of_expr expr'))
  | (E_bind expr5 expr') => ((is_expr_of_expr expr5) /\ (is_expr_of_expr expr'))
  | (E_function value_name5 expr5) => ((is_expr_of_expr expr5))
  | (E_let value_name5 expr5 expr') => ((is_expr_of_expr expr5) /\ (is_expr_of_expr expr'))
  | (E_live_expr expr5) => ((is_expr_of_expr expr5))
  | (E_dead_expr value5) => ((is_value_of_expr value5))
  | (E_pair e e') => ((is_expr_of_expr e) /\ (is_expr_of_expr e'))
  | (E_taggingleft e) => ((is_expr_of_expr e))
  | (E_taggingright e) => ((is_expr_of_expr e))
  | (E_case e1 x1 e2 x2 e3) => ((is_expr_of_expr e1) /\ (is_expr_of_expr e2) /\ (is_expr_of_expr e3))
end
with is_value_of_expr (e_5:expr) : Prop :=
  match e_5 with
  | (E_ident value_name5) => False
  | (E_constant constant5) => (True)
  | (E_apply expr5 expr') => False
  | (E_bind expr5 expr') => False
  | (E_function value_name5 expr5) => ((is_expr_of_expr expr5))
  | (E_let value_name5 expr5 expr') => False
  | (E_live_expr expr5) => False
  | (E_dead_expr value5) => False
  | (E_pair e e') => ((is_value_of_expr e) /\ (is_value_of_expr e'))
  | (E_taggingleft e) => ((is_value_of_expr e))
  | (E_taggingright e) => ((is_value_of_expr e))
  | (E_case e1 x1 e2 x2 e3) => False
end.

(** library functions *)
Fixpoint list_mem A (eq:forall a b:A,{a=b}+{a<>b}) (x:A) (l:list A) {struct l} : bool :=
  match l with
  | nil => false
  | cons h t => if eq h x then true else list_mem A eq x t
end.
Implicit Arguments list_mem.

Fixpoint list_assoc A B (eq:forall a b:A,{a=b}+{a<>b}) (x:A) (l:list (A*B)) {struct l} : option B :=
  match l with
  | nil => None
  | cons (a,b) t => if (eq a x) then Some b else list_assoc A B eq x t
end.
Implicit Arguments list_assoc.

Fixpoint list_minus2 A B (eq:forall a b:A,{a=b}+{a<>b}) (l1:list (A*B)) (l2:list A) {struct l1} : list (A*B) :=
  match l1 with
  | nil => nil
  | cons a t => if (list_mem (A:=A) eq (@fst A B a) l2) then list_minus2 A B eq t l2 else cons a (list_minus2 A B eq t l2)
end.
Implicit Arguments list_minus2.


(** substitutions *)
Fixpoint tsubst_typexpr (sub:list (typvar*typexpr)) (t_6:typexpr) {struct t_6} : typexpr :=
  match t_6 with
  | (TE_var typvar5) => (match list_assoc eq_typvar typvar5 sub with None => (TE_var typvar5) | Some t5 => t5 end)
  | (TE_arrow typexpr5 typexpr') => TE_arrow (tsubst_typexpr sub typexpr5) (tsubst_typexpr sub typexpr')
  | (TE_constr0 typeconstr5) => TE_constr0 typeconstr5
  | (TE_prod typexpr5 typexpr') => TE_prod (tsubst_typexpr sub typexpr5) (tsubst_typexpr sub typexpr')
  | (TE_concurrent typexpr5) => TE_concurrent (tsubst_typexpr sub typexpr5)
  | (TE_sum typexpr5 typexpr') => TE_sum (tsubst_typexpr sub typexpr5) (tsubst_typexpr sub typexpr')
end.

Definition tsubst_typscheme (sub:list (typvar*typexpr)) (ts5:typscheme) : typscheme :=
  match ts5 with
  | (TS_ts typvar_list typexpr5) => TS_ts typvar_list (tsubst_typexpr (list_minus2 eq_typvar sub (unmake_list_typvar typvar_list)) typexpr5)
end.

Fixpoint subst_expr (e_5:expr) (x_5:value_name) (e__6:expr) {struct e__6} : expr :=
  match e__6 with
  | (E_ident value_name5) => (if eq_value_name value_name5 x_5 then e_5 else (E_ident value_name5))
  | (E_constant constant5) => E_constant constant5
  | (E_apply expr5 expr') => E_apply (subst_expr e_5 x_5 expr5) (subst_expr e_5 x_5 expr')
  | (E_bind expr5 expr') => E_bind (subst_expr e_5 x_5 expr5) (subst_expr e_5 x_5 expr')
  | (E_function value_name5 expr5) => E_function value_name5 (if list_mem eq_value_name x_5 (cons value_name5 nil) then expr5 else (subst_expr e_5 x_5 expr5))
  | (E_let value_name5 expr5 expr') => E_let value_name5 (subst_expr e_5 x_5 expr5) (if list_mem eq_value_name x_5 (cons value_name5 nil) then expr' else (subst_expr e_5 x_5 expr'))
  | (E_live_expr expr5) => E_live_expr (subst_expr e_5 x_5 expr5)
  | (E_dead_expr value5) => E_dead_expr value5
  | (E_pair e e') => E_pair (subst_expr e_5 x_5 e) (subst_expr e_5 x_5 e')
  | (E_taggingleft e) => E_taggingleft (subst_expr e_5 x_5 e)
  | (E_taggingright e) => E_taggingright (subst_expr e_5 x_5 e)
  | (E_case e1 x1 e2 x2 e3) => E_case (subst_expr e_5 x_5 e1) x1 (subst_expr e_5 x_5 e2) x2 (subst_expr e_5 x_5 e3)
end.

Fixpoint tsubst_G (sub:list (typvar*typexpr)) (G_6:G) {struct G_6} : G :=
  match G_6 with
  | G_em => G_em 
  | (G_vn G5 value_name5 typscheme5) => G_vn (tsubst_G sub G5) value_name5 (tsubst_typscheme sub typscheme5)
end.

(** library functions *)
Fixpoint list_minus A (eq:forall a b:A,{a=b}+{a<>b}) (l1:list A) (l2:list A) {struct l1} : list A :=
  match l1 with
  | nil => nil
  | cons h t => if (list_mem (A:=A) eq h l2) then list_minus A eq t l2 else cons h (list_minus A eq t l2)
end.
Implicit Arguments list_minus.


(** free variables *)
Fixpoint ftv_typexpr (t5:typexpr) : list typvar :=
  match t5 with
  | (TE_var typvar5) => (cons typvar5 nil)
  | (TE_arrow typexpr5 typexpr') => (app (ftv_typexpr typexpr5) (ftv_typexpr typexpr'))
  | (TE_constr0 typeconstr5) => nil
  | (TE_prod typexpr5 typexpr') => (app (ftv_typexpr typexpr5) (ftv_typexpr typexpr'))
  | (TE_concurrent typexpr5) => ((ftv_typexpr typexpr5))
  | (TE_sum typexpr5 typexpr') => (app (ftv_typexpr typexpr5) (ftv_typexpr typexpr'))
end.

Definition ftv_typscheme (ts5:typscheme) : list typvar :=
  match ts5 with
  | (TS_ts typvar_list typexpr5) => (app nil (list_minus eq_typvar (ftv_typexpr typexpr5) (unmake_list_typvar typvar_list)))
end.

Fixpoint ftv_G (G_6:G) : list typvar :=
  match G_6 with
  | G_em => nil
  | (G_vn G5 value_name5 typscheme5) => (app (ftv_G G5) (ftv_typscheme typscheme5))
end.

Fixpoint remove_duplicates (l:list_typvar) : list_typvar :=
  match l with
  | Nil_list_typvar => Nil_list_typvar
  | Cons_list_typvar h t => 
    if (list_mem eq_typvar h (unmake_list_typvar t))  
    then remove_duplicates t
    else Cons_list_typvar h (remove_duplicates t)
end. 
(** definitions *)

(* defns Jtype *)
Inductive VTSin : value_name -> typscheme -> G -> Prop :=    (* defn VTSin *)
 | VTSin_vn1 : forall (value_name5:value_name) (typscheme5:typscheme) (G5:G),
     VTSin value_name5 typscheme5 (G_vn G5 value_name5 typscheme5)
 | VTSin_vn2 : forall (value_name5:value_name) (typscheme5:typscheme) (G5:G) (value_name':value_name) (typscheme':typscheme),
     VTSin value_name5 typscheme5 G5 ->
      not(  value_name5 = value_name'  )  ->
     VTSin value_name5 typscheme5 (G_vn G5 value_name' typscheme')
with G_constant : G -> constant -> typexpr -> Prop :=    (* defn G_constant *)
 | constant_int : forall (G5:G) (integer_literal5:integer_literal),
     G_constant G5 (CONST_int integer_literal5) (TE_constr0 TC_int)
 | constant_false : forall (G5:G),
     G_constant G5 CONST_false (TE_constr0 TC_bool)
 | constant_true : forall (G5:G),
     G_constant G5 CONST_true (TE_constr0 TC_bool)
 | constant_unit : forall (G5:G),
     G_constant G5 CONST_unit (TE_constr0 TC_unit)
 | constant_and : forall (G5:G),
     G_constant G5 CONST_and (TE_arrow (TE_constr0 TC_bool)  (TE_arrow (TE_constr0 TC_bool) (TE_constr0 TC_bool)) )
 | constant_not : forall (G5:G),
     G_constant G5 CONST_not (TE_arrow (TE_constr0 TC_bool) (TE_constr0 TC_bool))
 | constant_ret : forall (G5:G) (t:typexpr),
     G_constant G5 CONST_ret (TE_arrow t (TE_concurrent t))
 | constant_fork : forall (G5:G) (t1 t2:typexpr),
     G_constant G5 CONST_fork (TE_arrow  (TE_concurrent t1)   (TE_arrow  (TE_concurrent t2)   (TE_concurrent  (TE_sum  (TE_sum  (TE_prod t1 t2)   (TE_prod t1  (TE_concurrent t2) ) )   (TE_prod  (TE_concurrent t1)  t2) ) ) ) )
with Get : G -> expr -> typexpr -> Prop :=    (* defn Get *)
 | Get_value_name : forall (G5:G) (x:value_name) (t:typexpr) (typscheme5:typscheme),
     VTSin x typscheme5 G5 ->
      (exists tvs, exists txp, exists s, 
              typscheme5  = TS_ts tvs txp 
             /\ tvs = make_list_typvar
                    (List.map (fun (x:typvar*typexpr) => match x with (x1,x2) => x1 end) 
                              s)  
             /\ tsubst_typexpr s txp =  t )  ->
     Get G5 (E_ident x) t
 | Get_constant : forall (G5:G) (constant5:constant) (t:typexpr),
     G_constant G5 constant5 t ->
     Get G5 (E_constant constant5) t
 | Get_apply : forall (G5:G) (e e':expr) (t2 t1:typexpr),
     Get G5 e (TE_arrow t1 t2) ->
     Get G5 e' t1 ->
     Get G5 (E_apply e e') t2
 | Get_lambda : forall (G5:G) (x1:value_name) (e:expr) (t1 t:typexpr),
     Get (G_vn G5 x1 (TS_ts Nil_list_typvar t1)) e t ->
     Get G5 (E_function x1 e) (TE_arrow t1 t)
 | Get_live : forall (G5:G) (e:expr) (t:typexpr),
     Get G5 e t ->
     Get G5 (E_live_expr e) (TE_concurrent t)
 | Get_dead : forall (G5:G) (t:typexpr) (v:expr),
     is_value_of_expr v ->
     Get G5 v t ->
     Get G5 (E_dead_expr v) (TE_concurrent t)
 | Get_bind : forall (G5:G) (e e':expr) (t' t:typexpr),
     Get G5 e (TE_concurrent t) ->
     Get G5 e' (TE_arrow t (TE_concurrent t')) ->
     Get G5 (E_bind e e') (TE_concurrent t')
 | Get_pair : forall (G5:G) (e e':expr) (t1 t2:typexpr),
     Get G5 e t1 ->
     Get G5 e' t2 ->
     Get G5 (E_pair e e')  (TE_prod t1 t2) 
 | Get_let : forall (G5:G) (x:value_name) (e e':expr) (t' t:typexpr) (typscheme5:typscheme),
     Get G5 e t ->
     Get (G_vn G5 x typscheme5) e' t' ->
      typscheme5 =  (TS_ts (remove_duplicates (make_list_typvar (list_minus eq_typvar (ftv_typexpr  t ) (ftv_G  G5 ))))  t )   ->
     Get G5 (E_let x e e') t'
 | Get_TInl : forall (G5:G) (e:expr) (t t':typexpr),
     Get G5 e t ->
     Get G5 (E_taggingleft e) (TE_sum t t')
 | Get_TInr : forall (G5:G) (e:expr) (t' t:typexpr),
     Get G5 e t ->
     Get G5 (E_taggingright e) (TE_sum t' t)
 | Get_TCase : forall (G5:G) (e:expr) (x:value_name) (e':expr) (x':value_name) (e'':expr) (t'' t t':typexpr),
     Get G5 e (TE_sum t t') ->
     Get (G_vn G5 x (TS_ts Nil_list_typvar t)) e' t'' ->
     Get (G_vn G5 x' (TS_ts Nil_list_typvar t')) e'' t'' ->
     Get G5 (E_case e x e' x' e'') t''.
(** definitions *)

(* defns Jop *)
Inductive JO_red : expr -> expr -> Prop :=    (* defn red *)
 | JO_red_app : forall (x:value_name) (e v:expr),
     is_value_of_expr v ->
     JO_red (E_apply  (E_function x e)  v)  (subst_expr  v   x   e ) 
 | JO_red_let : forall (x:value_name) (e v:expr),
     is_value_of_expr v ->
     JO_red (E_let x v e)  (subst_expr  v   x   e ) 
 | JO_red_live : forall (e e':expr),
     JO_red e e' ->
     JO_red (E_live_expr e) (E_live_expr e')
 | JO_red_die : forall (v:expr),
     is_value_of_expr v ->
     JO_red (E_live_expr v) (E_dead_expr v)
 | JO_red_fork1 : forall (e e' e'':expr),
     JO_red e e'' ->
     JO_red (E_apply  (E_apply (E_constant CONST_fork) e)  e') (E_apply  (E_apply (E_constant CONST_fork) e'')  e')
 | JO_red_fork2 : forall (e e' e'':expr),
     JO_red e' e'' ->
     JO_red (E_apply  (E_apply (E_constant CONST_fork) e)  e') (E_apply  (E_apply (E_constant CONST_fork) e)  e'')
 | JO_red_forkdeath : forall (v v':expr),
     is_value_of_expr v ->
     is_value_of_expr v' ->
     JO_red (E_apply  (E_apply (E_constant CONST_fork) v)  v') (E_dead_expr (E_pair v v'))
 | JO_red_ret : forall (e:expr),
     JO_red (E_apply (E_constant CONST_ret) e) (E_live_expr e)
 | JO_red_evalbind : forall (e e'' e':expr),
     JO_red e e' ->
     JO_red (E_bind e e'') (E_bind e' e'')
 | JO_red_dobind : forall (e v:expr),
     is_value_of_expr v ->
     JO_red (E_bind (E_dead_expr v) e) (E_apply e v)
 | JO_red_context_app1 : forall (e e1 e':expr),
     JO_red e e' ->
     JO_red (E_apply e e1) (E_apply e' e1)
 | JO_red_context_app2 : forall (v e e':expr),
     is_value_of_expr v ->
     JO_red e e' ->
     JO_red (E_apply v e) (E_apply v e')
 | JO_red_context_let : forall (x:value_name) (e e1 e':expr),
     JO_red e e' ->
     JO_red (E_let x e e1) (E_let x e' e1)
 | JO_red_not_1 : 
     JO_red (E_apply (E_constant CONST_not) (E_constant CONST_true)) (E_constant CONST_false)
 | JO_red_not_2 : 
     JO_red (E_apply (E_constant CONST_not) (E_constant CONST_false)) (E_constant CONST_true)
 | JO_red_and_1 : forall (e:expr),
     JO_red (E_apply  (E_apply (E_constant CONST_and) (E_constant CONST_true))  e) e
 | JO_red_and_2 : forall (e:expr),
     JO_red (E_apply  (E_apply (E_constant CONST_and) (E_constant CONST_false))  e) (E_constant CONST_false)
 | JO_red_pair_1 : forall (e e'' e':expr),
     JO_red e e' ->
     JO_red (E_pair e e'') (E_pair e' e'')
 | JO_red_pair_2 : forall (v e e':expr),
     is_value_of_expr v ->
     JO_red e e' ->
     JO_red (E_pair v e) (E_pair v e')
 | JO_red_evalinl : forall (e e':expr),
     JO_red e e' ->
     JO_red (E_taggingleft e) (E_taggingleft e')
 | JO_red_evalinr : forall (e e':expr),
     JO_red e e' ->
     JO_red (E_taggingright e) (E_taggingright e')
 | JO_red_evalcaseinl : forall (x:value_name) (e:expr) (x':value_name) (e' v:expr),
     is_value_of_expr v ->
     JO_red (E_case  (E_taggingleft v)  x e x' e')  (subst_expr  v   x   e ) 
 | JO_red_evalcaseinr : forall (x:value_name) (e:expr) (x':value_name) (e' v:expr),
     is_value_of_expr v ->
     JO_red (E_case  (E_taggingright v)  x e x' e')  (subst_expr  v   x'   e' ) 
 | JO_red_evalcase : forall (e:expr) (x:value_name) (e'':expr) (x':value_name) (e''' e':expr),
     JO_red e e' ->
     JO_red (E_case e x e'' x' e''') (E_case e' x e'' x' e''').


