Require Import Coq.Strings.String.
Open Scope string_scope.

Require Import Coq.Lists.List.
Open Scope list_scope.

Definition var := string.

(* Lambda calculus syntax *)
Inductive Exp : Type :=
  | ref : var -> Exp
  | abs : var -> Exp -> Exp
  | app : Exp -> Exp -> Exp.

Definition id := (abs "x" (ref "x")).
Definition x := (ref "x").
Definition y := (ref "y").
Definition f := (abs "f" (app (ref "f") (ref "f"))).

Inductive Beta : var -> Exp -> Exp -> Exp -> Prop :=
  | beta_ref_eq : forall v e2, Beta v (ref v) e2 e2
  | beta_ref_neq : forall v v' e2, v <> v' -> Beta v (ref v') e2 (ref v') 
  | beta_abs_eq : forall v e1 e2, Beta v (abs v e1) e2 (abs v e1)
  | beta_abs_neq : forall v v' e1 e2 e1', v <> v' -> Beta v e1 e2 e1' -> Beta v (abs v' e1) e2 (abs v' e1')
  | beta_app : forall v e0 e0' e1 e1' e2, Beta v e0 e2 e0' -> Beta v e1 e2 e1' -> Beta v (app e0 e1) e2 (app e0' e1').

Inductive Step : Exp -> Exp -> Prop :=
  | stp_abs          : forall {v e e'},            Step e e' -> Step (abs v e) (abs v e')
  | stp_app_e1       : forall {e11 e12 e1' e2},    Step (app e11 e12) e1' -> Step (app (app e11 e12) e2) (app e1' e2)
  | stp_app_abs_e2   : forall {v e11 e21 e22 e2'}, Step (app e21 e22) e2' -> Step (app (abs v e11) (app e21 e22)) (app (abs v e11) e2')
  | stp_app_ref_e2   : forall {v e21 e22 e2'},     Step (app e21 e22) e2' -> Step (app (ref v)     (app e21 e22)) (app (ref v)     e2')
  | stp_app_abs_beta : forall {v e11 v2 e21 e3},   Beta v e11 (abs v2 e21) e3 -> Step (app (abs v e11) (abs v2 e21)) e3
  | stp_app_ref_beta : forall {v e11 v2 e3},       Beta v e11 (ref v2)     e3 -> Step (app (abs v e11) (ref v2))     e3.

Fixpoint alpha_conv (v:var) (s:var) (e:Exp) : Exp :=
  match e with
  | (ref t) => if string_dec v t then (ref s) else (ref t)
  | (abs t e1) => if string_dec v t then (abs s (alpha_conv v s e1)) else (abs t (alpha_conv v s e1))
  | (app e1 e2) => app (alpha_conv v s e1) (alpha_conv v s e2)
  end.

Fixpoint subst' (v : var) (e1 : Exp) (e2 : Exp) : Exp := 
  match e1 with
  | (ref v') => if string_dec v v' then e2 else (ref v') 
  | (abs v' e1') => if string_dec v v' then e1 else (abs v' (subst' v e1' e2))
  | (app e11 e12) => (app (subst' v e11 e2) (subst' v e12 e2))
  end.

Check List.app.

Fixpoint get_name_list (e : Exp) : list string :=
  match e with
  | (ref v) => cons v nil
  | (abs v e1) => remove string_dec v (get_name_list e1)
  | (app e1 e2) => List.app (get_name_list e1) (get_name_list e2)
  end.

Local Open Scope char_scope.
Definition char_prime := "'".
Close Scope char_scope.

Fixpoint rename_str (v:string) (s:string) : string :=
  match s with
  | EmptyString => "'"
  | String a s' => 
    match v with
    | EmptyString => if prefix "'" s then String char_prime (rename_str EmptyString s') else "'"
    | String a v' => String a (rename_str v' s')
    end
  end.

Eval compute in rename_str "s" "s'".

Fixpoint rename_list (v:string) (l:list string) : string :=
  match l with
  | nil => v
  | (cons s t) => let v' := rename_list v t in
    if prefix v' s then rename_str v' s
    else v'
  end.

Import ListNotations.

Eval compute in rename_list "s" [ "s"; "s'"; "x"; "s'''"].

Fixpoint rename_exp_for_list (ls:list string) (e:Exp) : Exp :=
  match ls with
  | nil => e
  | (cons s l) => rename_exp_for_list l (alpha_conv s (rename_list s ls) e)
  end.



Fixpoint subst (v : var) (e1 : Exp) (e2 : Exp) : Exp :=
  let e1' := rename_exp_for_list (remove string_dec v (get_name_list e2)) e1 in subst' v e1' e2.

Eval compute in (subst "f" (abs "x" (abs "y" (ref "f"))) id).

Eval compute in (subst "x" (ref "x") id).

Fixpoint step (e : Exp) : Exp :=
  match e with
  | (ref v) => ref v
  | (abs v e') => abs v (step e')
  | (app (abs v1 e11) e2) => subst v1 e11 (step e2)
  | (app (ref v1) e2) => (app (ref v1) (step e2))
  | (app e1 e2) => app (step e1) (step e2)
  end.

Fixpoint stepN (n:nat) (e:Exp) : Exp :=
  match n with
  | O => e
  | S x => stepN x (step e)
  end.

Definition YC := (abs "f" (app 
  (abs "x" (app 
    (ref "f") 
    (app (ref "x") (ref "x"))))
  (abs "x" (app 
    (ref "f") 
    (app (ref "x") (ref "x")))))).

Definition f1 := (step (app YC id)).
Definition f2 := (step f1).
Definition f3 := (step f2).
Definition f4 := (step f3).
Definition f5 := (step f4).

Eval compute in f1.
Eval compute in f2.
Eval compute in f3.
Eval compute in f4.
Eval compute in f5.

Eval compute in remove string_dec "y" (get_name_list (ref "x")).
Eval compute in rename_exp_for_list ["x"] (abs "x" (ref "y")).
Eval compute in (rename_list "x" ["x"]).
Eval compute in (alpha_conv "x" "x'" (abs "x" (ref "y"))).
Eval compute in 
  (step (abs "x" (app (abs "y" (abs "x" (ref "y"))) (ref "x")))).
Eval compute in step
  (app (abs "x" (abs "x'" (app (ref "x'") (ref "x")))) (ref "x'")).
Eval compute in stepN 2
  (app (app (abs "x" (abs "x'" (app (ref "x'") (ref "x")))) (ref "x'")) id).

Eval compute in 
  (step (app (abs "y" (abs "a" (ref "y"))) (ref "a"))).

Eval compute in stepN 1 (app (abs "y" (ref "x")) (ref "x")).


