type nat =
| O
| S of nat

type sumbool =
| Left
| Right

type var = nat

(** val eq_var : var -> var -> sumbool **)

let rec eq_var n y0 =
  match n with
  | O ->
    (match y0 with
     | O -> Left
     | S n0 -> Right)
  | S n0 ->
    (match y0 with
     | O -> Right
     | S n1 -> eq_var n0 n1)

type term =
| T_var of var
| T_app of term * term
| T_idapp
| T_selapp
| T_subapp

(** val tsubst_term : term -> var -> term -> term **)

let rec tsubst_term t5 x5 = function
| T_var x ->
  (match eq_var x x5 with
   | Left -> t5
   | Right -> T_var x)
| T_app (t, t') -> T_app ((tsubst_term t5 x5 t), (tsubst_term t5 x5 t'))
| x -> x

(* reduce : logical inductive *)
(* with constructors : id_app sel_app sub_app
ctx_app_fun *)


