(* generated by Ott 0.23 from: mconbase.ott *)

Require Import Arith.
Require Import Bool.
Require Import List.


Definition value_name := nat.
Lemma eq_value_name: forall (x y : value_name), {x = y} + {x <> y}.
Proof.
  decide equality; auto with ott_coq_equality arith.
Defined.
Hint Resolve eq_value_name : ott_coq_equality.
Definition label := nat.
Lemma eq_label: forall (x y : label), {x = y} + {x <> y}.
Proof.
  decide equality; auto with ott_coq_equality arith.
Defined.
Hint Resolve eq_label : ott_coq_equality.
Definition ident := nat.
Definition index := nat.

Inductive typvar : Set := 
 | TV_ident (ident5:ident).

Inductive typconst : Set := 
 | TC_unit : typconst.

Inductive typexpr : Set := 
 | TE_constants (typconst5:typconst)
 | TE_var (typvar5:typvar)
 | TE_arrow (typexpr5:typexpr) (typexpr':typexpr)
 | TE_prod (typexpr5:typexpr) (typexpr':typexpr)
 | TE_concurrent (typexpr5:typexpr)
 | TE_sum (typexpr5:typexpr) (typexpr':typexpr).

Inductive constant : Set := 
 | CONST_ret : constant
 | CONST_fork : constant
 | CONST_unit : constant
 | CONST_stop : constant.

Inductive redlabel : Set := 
 | RL_tau : redlabel
 | RL_labelled (lab:label).

Inductive list_typvar : Set := 
 | Nil_list_typvar : list_typvar
 | Cons_list_typvar (_:typvar) (_:list_typvar).

Inductive livemodes : Set := 
 | LM_comp (rl:redlabel)
 | LM_expr (expr5:expr)
with expr : Set := 
 | E_ident (value_name5:value_name)
 | E_constant (constant5:constant)
 | E_apply (expr5:expr) (expr':expr)
 | E_bind (expr5:expr) (expr':expr)
 | E_function (value_name5:value_name) (typexpr5:typexpr) (expr5:expr)
 | E_fix (e:expr)
 | E_live_expr (lm:livemodes)
 | E_pair (e:expr) (e':expr)
 | E_taggingleft (e:expr)
 | E_taggingright (e:expr)
 | E_case (e1:expr) (x1:value_name) (e2:expr) (x2:value_name) (e3:expr).

Inductive typscheme : Set := 
 | TS_ts (_:list_typvar) (typexpr5:typexpr).

Inductive select : Set := 
 | S_First : select
 | S_Second : select.

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
Fixpoint is_value_of_expr (e_5:expr) : Prop :=
  match e_5 with
  | (E_ident value_name5) => False
  | (E_constant constant5) => (True)
(* Manual change *)
  | (E_apply expr5 expr') => match expr5 with | E_constant (CONST_fork) => is_value_of_expr (expr') | _ => False end
  | (E_bind expr5 expr') => False
  | (E_function value_name5 typexpr5 expr5) => (True)
  | (E_fix e) => ((is_value_of_expr e))
  | (E_live_expr lm) => (True)
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
  | (TE_constants typconst5) => TE_constants typconst5
  | (TE_var typvar5) => (match list_assoc eq_typvar typvar5 sub with None => (TE_var typvar5) | Some t5 => t5 end)
  | (TE_arrow typexpr5 typexpr') => TE_arrow (tsubst_typexpr sub typexpr5) (tsubst_typexpr sub typexpr')
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
  | (E_function value_name5 typexpr5 expr5) => E_function value_name5 typexpr5 (if list_mem eq_value_name x_5 (cons value_name5 nil) then expr5 else (subst_expr e_5 x_5 expr5))
  | (E_fix e) => E_fix (subst_expr e_5 x_5 e)
  | (E_live_expr lm) => E_live_expr (subst_livemodes e_5 x_5 lm)
  | (E_pair e e') => E_pair (subst_expr e_5 x_5 e) (subst_expr e_5 x_5 e')
  | (E_taggingleft e) => E_taggingleft (subst_expr e_5 x_5 e)
  | (E_taggingright e) => E_taggingright (subst_expr e_5 x_5 e)
  | (E_case e1 x1 e2 x2 e3) => E_case (subst_expr e_5 x_5 e1) x1 (subst_expr e_5 x_5 e2) x2 (subst_expr e_5 x_5 e3)
end
with subst_livemodes (e5:expr) (x5:value_name) (lm5:livemodes) {struct lm5} : livemodes :=
  match lm5 with
  | (LM_comp rl) => LM_comp rl
  | (LM_expr expr5) => LM_expr (subst_expr e5 x5 expr5)
end.

Fixpoint tsubst_expr (sub:list (typvar*typexpr)) (e_5:expr) {struct e_5} : expr :=
  match e_5 with
  | (E_ident value_name5) => E_ident value_name5
  | (E_constant constant5) => E_constant constant5
  | (E_apply expr5 expr') => E_apply (tsubst_expr sub expr5) (tsubst_expr sub expr')
  | (E_bind expr5 expr') => E_bind (tsubst_expr sub expr5) (tsubst_expr sub expr')
  | (E_function value_name5 typexpr5 expr5) => E_function value_name5 (tsubst_typexpr sub typexpr5) (tsubst_expr sub expr5)
  | (E_fix e) => E_fix (tsubst_expr sub e)
  | (E_live_expr lm) => E_live_expr (tsubst_livemodes sub lm)
  | (E_pair e e') => E_pair (tsubst_expr sub e) (tsubst_expr sub e')
  | (E_taggingleft e) => E_taggingleft (tsubst_expr sub e)
  | (E_taggingright e) => E_taggingright (tsubst_expr sub e)
  | (E_case e1 x1 e2 x2 e3) => E_case (tsubst_expr sub e1) x1 (tsubst_expr sub e2) x2 (tsubst_expr sub e3)
end
with tsubst_livemodes (sub:list (typvar*typexpr)) (lm5:livemodes) {struct lm5} : livemodes :=
  match lm5 with
  | (LM_comp rl) => LM_comp rl
  | (LM_expr expr5) => LM_expr (tsubst_expr sub expr5)
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
  | (TE_constants typconst5) => nil
  | (TE_var typvar5) => (cons typvar5 nil)
  | (TE_arrow typexpr5 typexpr') => (app (ftv_typexpr typexpr5) (ftv_typexpr typexpr'))
  | (TE_prod typexpr5 typexpr') => (app (ftv_typexpr typexpr5) (ftv_typexpr typexpr'))
  | (TE_concurrent typexpr5) => ((ftv_typexpr typexpr5))
  | (TE_sum typexpr5 typexpr') => (app (ftv_typexpr typexpr5) (ftv_typexpr typexpr'))
end.

Definition ftv_typscheme (ts5:typscheme) : list typvar :=
  match ts5 with
  | (TS_ts typvar_list typexpr5) => (app nil (list_minus eq_typvar (ftv_typexpr typexpr5) (unmake_list_typvar typvar_list)))
end.

Fixpoint ftv_expr (e_5:expr) : list typvar :=
  match e_5 with
  | (E_ident value_name5) => nil
  | (E_constant constant5) => nil
  | (E_apply expr5 expr') => (app (ftv_expr expr5) (ftv_expr expr'))
  | (E_bind expr5 expr') => (app (ftv_expr expr5) (ftv_expr expr'))
  | (E_function value_name5 typexpr5 expr5) => (app (ftv_typexpr typexpr5) (ftv_expr expr5))
  | (E_fix e) => ((ftv_expr e))
  | (E_live_expr lm) => ((ftv_livemodes lm))
  | (E_pair e e') => (app (ftv_expr e) (ftv_expr e'))
  | (E_taggingleft e) => ((ftv_expr e))
  | (E_taggingright e) => ((ftv_expr e))
  | (E_case e1 x1 e2 x2 e3) => (app (ftv_expr e1) (app (ftv_expr e2) (ftv_expr e3)))
end
with ftv_livemodes (lm5:livemodes) : list typvar :=
  match lm5 with
  | (LM_comp rl) => nil
  | (LM_expr expr5) => ((ftv_expr expr5))
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
 | constant_ret : forall (G5:G) (t:typexpr),
     G_constant G5 CONST_ret (TE_arrow t (TE_concurrent t))
 | constant_fork : forall (G5:G) (t1 t2:typexpr),
     G_constant G5 CONST_fork (TE_arrow  (TE_concurrent t1)   (TE_arrow  (TE_concurrent t2)   (TE_concurrent  (TE_sum  (TE_sum  (TE_prod t1 t2)   (TE_prod t1  (TE_concurrent t2) ) )   (TE_prod  (TE_concurrent t1)  t2) ) ) ) )
 | constant_unit : forall (G5:G),
     G_constant G5 CONST_unit (TE_constants TC_unit)
 | constant_stop : forall (G5:G) (t:typexpr),
     G_constant G5 CONST_stop t
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
 | Get_lambda : forall (G5:G) (x1:value_name) (t1:typexpr) (e:expr) (t:typexpr),
     Get (G_vn G5 x1 (TS_ts Nil_list_typvar t1)) e t ->
     Get G5 (E_function x1 t1 e) (TE_arrow t1 t)
 | Get_live_exp : forall (G5:G) (e:expr) (t:typexpr),
     Get G5 e t ->
     Get G5 (E_live_expr (LM_expr e)) (TE_concurrent t)
 | Get_live_comp : forall (G5:G) (rl:redlabel),
     Get G5 (E_live_expr  (LM_comp rl) ) (TE_concurrent (TE_constants TC_unit))
 | Get_fix : forall (G5:G) (e:expr) (t t':typexpr),
     Get G5 e (TE_arrow  (TE_arrow t t')   (TE_arrow t t') ) ->
     Get G5 (E_fix e)  (TE_arrow t t') 
 | Get_bind : forall (G5:G) (e e':expr) (t' t:typexpr),
     Get G5 e (TE_concurrent t) ->
     Get G5 e' (TE_arrow t (TE_concurrent t')) ->
     Get G5 (E_bind e e') (TE_concurrent t')
 | Get_pair : forall (G5:G) (e e':expr) (t1 t2:typexpr),
     Get G5 e t1 ->
     Get G5 e' t2 ->
     Get G5 (E_pair e e')  (TE_prod t1 t2) 
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
Inductive JO_red : expr -> select -> redlabel -> expr -> Prop :=    (* defn red *)
 | JO_red_app : forall (x:value_name) (t:typexpr) (e:expr) (s:select) (v:expr),
     is_value_of_expr v ->
     JO_red (E_apply  (E_function x t e)  v) s RL_tau  (subst_expr  v   x   e ) 
 | JO_red_forkmove1 : forall (e e':expr) (rl:redlabel) (e'':expr) (s:select),
     ~ ( is_value_of_expr ( e' ) )  ->
     JO_red e s rl e'' ->
     JO_red (E_apply  (E_apply (E_constant CONST_fork)  (E_live_expr (LM_expr e)) )   (E_live_expr (LM_expr e')) ) S_First rl (E_apply  (E_apply (E_constant CONST_fork)  (E_live_expr (LM_expr e'')) )   (E_live_expr (LM_expr e')) )
 | JO_red_forkmove2 : forall (e e':expr) (rl:redlabel) (e'':expr) (s:select),
     ~ ( is_value_of_expr ( e ) )  ->
     JO_red e' s rl e'' ->
     JO_red (E_apply  (E_apply (E_constant CONST_fork)  (E_live_expr (LM_expr e)) )   (E_live_expr (LM_expr e')) ) S_Second rl (E_apply  (E_apply (E_constant CONST_fork)  (E_live_expr (LM_expr e)) )   (E_live_expr (LM_expr e'')) )
 | JO_red_forkdeath1 : forall (v e:expr) (s:select),
     is_value_of_expr v ->
     JO_red (E_apply  (E_apply (E_constant CONST_fork)  (E_live_expr (LM_expr v)) )   (E_live_expr (LM_expr e)) ) s RL_tau (E_live_expr (LM_expr  (E_taggingleft  (E_taggingright  (E_pair v  (E_live_expr (LM_expr e)) ) ) ) ))
 | JO_red_forkdeath2 : forall (e v':expr) (s:select),
     is_value_of_expr v' ->
     JO_red (E_apply  (E_apply (E_constant CONST_fork)  (E_live_expr (LM_expr e)) )   (E_live_expr (LM_expr v')) ) s RL_tau (E_live_expr (LM_expr  (E_taggingright  (E_pair  (E_live_expr (LM_expr e))  v') ) ))
 | JO_red_forkdeath12 : forall (v v':expr) (s:select),
     is_value_of_expr v ->
     is_value_of_expr v' ->
     JO_red (E_apply  (E_apply (E_constant CONST_fork)  (E_live_expr (LM_expr v)) )   (E_live_expr (LM_expr v')) ) s RL_tau (E_live_expr (LM_expr  (E_taggingleft  (E_taggingleft  (E_pair v v') ) ) ))
 | JO_red_forkdocomp1 : forall (rl:redlabel) (e:expr) (s:select),
     JO_red (E_apply  (E_apply (E_constant CONST_fork)  (E_live_expr  (LM_comp rl) ) )   (E_live_expr (LM_expr e)) ) s rl (E_live_expr (LM_expr  (E_taggingleft  (E_taggingright  (E_pair (E_constant CONST_unit)  (E_live_expr (LM_expr e)) ) ) ) ))
 | JO_red_forkdocomp2 : forall (e:expr) (rl:redlabel) (s:select),
     JO_red (E_apply  (E_apply (E_constant CONST_fork)  (E_live_expr (LM_expr e)) )   (E_live_expr  (LM_comp rl) ) ) s rl (E_live_expr (LM_expr  (E_taggingright  (E_pair  (E_live_expr (LM_expr e))  (E_constant CONST_unit)) ) ))
 | JO_red_forkdocomp12 : forall (rl rl':redlabel),
     JO_red (E_apply  (E_apply (E_constant CONST_fork)  (E_live_expr  (LM_comp rl) ) )   (E_live_expr  (LM_comp rl') ) ) S_First rl (E_apply  (E_apply (E_constant CONST_fork)  (E_live_expr  (LM_expr (E_constant CONST_unit)) ) )   (E_live_expr  (LM_comp rl') ) )
 | JO_red_forkdocomp21 : forall (rl rl':redlabel),
     JO_red (E_apply  (E_apply (E_constant CONST_fork)  (E_live_expr  (LM_comp rl) ) )   (E_live_expr  (LM_comp rl') ) ) S_Second rl' (E_apply  (E_apply (E_constant CONST_fork)  (E_live_expr  (LM_comp rl) ) )   (E_live_expr  (LM_expr (E_constant CONST_unit)) ) )
 | JO_red_forkfincomp12 : forall (rl':redlabel) (s:select),
     JO_red (E_apply  (E_apply (E_constant CONST_fork)  (E_live_expr  (LM_expr (E_constant CONST_unit)) ) )   (E_live_expr  (LM_comp rl') ) ) s rl' (E_live_expr (LM_expr  (E_taggingleft  (E_taggingleft  (E_pair (E_constant CONST_unit) (E_constant CONST_unit)) ) ) ))
 | JO_red_forkfincomp21 : forall (rl:redlabel) (s:select),
     JO_red (E_apply  (E_apply (E_constant CONST_fork)  (E_live_expr  (LM_comp rl) ) )   (E_live_expr  (LM_expr (E_constant CONST_unit)) ) ) s rl (E_live_expr (LM_expr  (E_taggingleft  (E_taggingleft  (E_pair (E_constant CONST_unit) (E_constant CONST_unit)) ) ) ))
 | JO_red_ret : forall (v:expr) (s:select),
     is_value_of_expr v ->
     JO_red (E_apply (E_constant CONST_ret) v) s RL_tau  (E_live_expr (LM_expr v)) 
 | JO_red_evalbind : forall (e e'':expr) (s:select) (rl:redlabel) (e':expr),
     JO_red e s rl e' ->
     JO_red (E_bind e e'') s rl (E_bind e' e'')
 | JO_red_movebind : forall (e e'':expr) (s:select) (rl:redlabel) (e':expr),
     JO_red e s rl e' ->
     JO_red (E_bind  (E_live_expr (LM_expr e))  e'') s rl (E_bind  (E_live_expr (LM_expr e'))  e'')
 | JO_red_compbind : forall (rl:redlabel) (e:expr) (s:select) (e':expr),
     JO_red (E_bind  (E_live_expr  (LM_comp rl) )  e) s rl (E_apply e' (E_constant CONST_unit))
 | JO_red_dobind : forall (v e:expr) (s:select),
     is_value_of_expr v ->
     JO_red (E_bind  (E_live_expr (LM_expr v))  e) s RL_tau (E_apply e v)
 | JO_red_context_app1 : forall (e e':expr) (s:select) (rl:redlabel) (e'':expr),
     JO_red e' s rl e'' ->
     JO_red (E_apply e e') s rl (E_apply e e'')
 | JO_red_context_app2 : forall (e v:expr) (s:select) (rl:redlabel) (e':expr),
     is_value_of_expr v ->
     JO_red e s rl e' ->
     JO_red (E_apply e v) s rl (E_apply e' v)
 | JO_red_fix_move : forall (e:expr) (s:select) (rl:redlabel) (e':expr),
     JO_red e s rl e' ->
     JO_red  (E_fix e)  s rl  (E_fix e') 
 | JO_red_fix_app : forall (v v':expr) (s:select),
     is_value_of_expr v ->
     is_value_of_expr v' ->
     JO_red (E_apply  (E_fix v)  v') s RL_tau (E_apply  (E_apply v  (E_fix v) )   v' )
 | JO_red_pair_1 : forall (e e'':expr) (s:select) (rl:redlabel) (e':expr),
     JO_red e s rl e' ->
     JO_red (E_pair e e'') s rl (E_pair e' e'')
 | JO_red_pair_2 : forall (v e:expr) (s:select) (rl:redlabel) (e':expr),
     is_value_of_expr v ->
     JO_red e s rl e' ->
     JO_red (E_pair v e) s rl (E_pair v e')
 | JO_red_evalinl : forall (e:expr) (s:select) (rl:redlabel) (e':expr),
     JO_red e s rl e' ->
     JO_red (E_taggingleft e) s rl (E_taggingleft e')
 | JO_red_evalinr : forall (e:expr) (s:select) (rl:redlabel) (e':expr),
     JO_red e s rl e' ->
     JO_red (E_taggingright e) s rl (E_taggingright e')
 | JO_red_evalcaseinl : forall (x:value_name) (e:expr) (x':value_name) (e':expr) (s:select) (v:expr),
     is_value_of_expr v ->
     JO_red (E_case  (E_taggingleft v)  x e x' e') s RL_tau  (subst_expr  v   x   e ) 
 | JO_red_evalcaseinr : forall (x:value_name) (e:expr) (x':value_name) (e':expr) (s:select) (v:expr),
     is_value_of_expr v ->
     JO_red (E_case  (E_taggingright v)  x e x' e') s RL_tau  (subst_expr  v   x'   e' ) 
 | JO_red_evalcase : forall (e:expr) (x:value_name) (e'':expr) (x':value_name) (e''':expr) (s:select) (rl:redlabel) (e':expr),
     JO_red e s rl e' ->
     JO_red (E_case e x e'' x' e''') s rl (E_case e' x e'' x' e''').


