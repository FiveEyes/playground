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

Fixpoint beta (v : var) (e1 : Exp) (e2 : Exp) : Exp :=
  match e1 with
  | (ref v') => if string_dec v v' then e2 else (ref v') 
  | (abs v' e1') => if string_dec v v' then (abs v' e1') else (abs v' (beta v e1' e2))
  | (app e11 e12) => (app (beta v e11 e2) (beta v e12 e2))
  end.

Eval compute in (beta "f" (abs "x" (abs "y" (ref "f"))) id).

Eval compute in (beta "x" (ref "x") id).

Fixpoint step (e : Exp) : Exp :=
  match e with
  | (ref v) => ref v
  | (abs v e') => abs v (step e')
  | (app (abs v1 e11) e2) => beta v1 e11 (step e2)
  | (app (ref v1) e2) => (app (ref v1) (step e2))
  | (app e1 e2) => app (step e1) (step e2)
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



