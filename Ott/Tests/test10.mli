type nat =
| O
| S of nat

type sumbool =
| Left
| Right

type var = nat

val eq_var : var -> var -> sumbool

type term =
| T_var of var
| T_app of term * term
| T_idapp
| T_selapp
| T_subapp

val tsubst_term : term -> var -> term -> term

(* reduce : logical inductive *)
(* with constructors : id_app sel_app sub_app
ctx_app_fun *)


