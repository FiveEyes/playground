(* Only P1 P2 Preservation and Sound are written by me *)

Inductive Exp : Type :=
  | litN : nat  -> Exp
  | litB : bool -> Exp
  | add  : Exp -> Exp -> Exp
  | cond : Exp -> Exp -> Exp -> Exp.

(* Types *)
Inductive T : Type :=
  | t_nat  : T
  | t_bool : T.

(* Operational semantics, one-step relation *)
Inductive Step : Exp -> Exp -> Prop :=

  | r_add : forall {n1 n2 n3},
      n3 = n1 + n2 -> Step (add (litN n1) (litN n2)) (litN n3)

  | r_cond_true : forall {e1 e2},
      Step (cond (litB true) e1 e2) e1

  | r_cond_false : forall {e1 e2},
      Step (cond (litB false) e1 e2) e2

  | c_add_l : forall {e1 e1' e2},
      Step e1 e1' -> Step (add e1 e2) (add e1' e2)

  | c_add_r : forall {e1 e2 e2'},
      Step e2 e2' -> Step (add e1 e2) (add e1 e2')

  | c_cond : forall {e1 e1' e2 e3},
      Step e1 e1' -> Step (cond e1 e2 e3) (cond e1' e2 e3).

(* Reflexive, transitive closure of Step *)
Inductive Sem : Exp -> Exp -> Prop :=

  | s_refl : forall {e},
      Sem e e

  | s_trans : forall {e1} e2 {e3},
      Step e1 e2 -> Sem e2 e3 -> Sem e1 e3.

(* Example expression *)
Definition ex1 :=
  add (cond (cond (litB false)
                  (litB false) (litB true))
            (litN 2) (litN 3))
      (litN 4).

(* Example semantic derivation *)
Fact s_ex1 : Sem ex1 (litN 6).
Proof.
  unfold ex1.
  apply s_trans with (e2 := add (cond (litB true) (litN 2) (litN 3)) (litN 4)).
    apply c_add_l. apply c_cond. apply r_cond_false.
  apply s_trans with (e2 := add (litN 2) (litN 4)).
    apply c_add_l. apply r_cond_true.
  apply s_trans with (e2 := litN 6).
    apply r_add. compute. reflexivity.
  apply s_refl.
Qed.

(* Typing relation *)
Inductive HasT : Exp -> T -> Prop :=

  | t_litN : forall {n},
      HasT (litN n) t_nat

  | t_litB : forall {b},
      HasT (litB b) t_bool

  | t_add  : forall {e1 e2},
      HasT e1 t_nat -> HasT e2 t_nat -> HasT (add e1 e2) t_nat

  | t_cond : forall {e1 e2 e3 t},
      HasT e1 t_bool -> HasT e2 t -> HasT e3 t -> HasT (cond e1 e2 e3) t.

(* Example typing derivation *)
Fact t_ex1 : HasT ex1 t_nat.
Proof.
  unfold ex1.
  apply t_add.
  apply t_cond.
  apply t_cond.
  apply t_litB. apply t_litB. apply t_litB.
  apply t_litN. apply t_litN. apply t_litN.
Qed.

(* Predicate indicating whether an expression is a value
   of the corresponding type *)
Inductive Value : Exp -> T -> Prop :=
  | v_litN : forall {n}, Value (litN n) t_nat
  | v_litB : forall {b}, Value (litB b) t_bool.

(* Progress: a well-typed term is not stuck *)
Lemma Progress : forall e t,
  HasT e t -> Value e t \/ (exists e', Step e e').
Proof.
  intros.
  induction H.

    (* litN *)
    left. exact v_litN.

    (* litB *)
    left. exact v_litB.

    (* add *)
    right. inversion IHHasT1.
      inversion IHHasT2.
        inversion H1; inversion H2.
          exists (litN (n+n0)).
          apply r_add. reflexivity.
        destruct H2.
          exists (add e1 x).
          apply c_add_r. apply H2.
        destruct H1.
          exists (add x e2).
          apply c_add_l. apply H1.

    (* cond *)
    right. inversion IHHasT1.
      inversion H2.
        destruct b.
          exists e2. apply r_cond_true.
          exists e3. apply r_cond_false.
        destruct H2.
          exists (cond x e2 e3).
            apply c_cond. apply H2.

Qed. (* Whew! *)

Ltac inv_auto H := inversion H; auto.

Lemma P1 : forall e1 e2,
  HasT e1 t_bool -> Step e1 e2 -> HasT e2 t_bool.
Proof.
  intros.
  induction H0; [inv_auto H | inv_auto H | inv_auto H | inv_auto H | inv_auto H | idtac].
  apply t_cond; [apply IHStep; inv_auto H | inv_auto H | inv_auto H].
Qed.

Lemma P2 : forall e1 e2,
  HasT e1 t_nat -> Step e1 e2 -> HasT e2 t_nat.
Proof.
  intros.
  induction H0;
  [apply t_litN | inv_auto H | inv_auto H | apply t_add; inv_auto H | apply t_add; inv_auto H | idtac].
  apply t_cond; [apply P1 with (e1 := e1); inv_auto H | inv_auto H | inv_auto H].
Qed.

(* Preservation: if a term is well-typed before a step,
   then it is well-typed after a step. *)
Lemma Preservation : forall e1 e2 t1,
  HasT e1 t1 -> Step e1 e2 -> (exists t2, HasT e2 t2).
Proof.
  intros.
  exists t1.
  destruct t1.
  apply P2 with (e1 := e1); auto.
  apply P1 with (e1 := e1); auto.
Qed.

(* Soundness: the type system is sound if it ensures progress
   and preservation. *)
Theorem Sound : forall e e' t,
  HasT e t -> (Value e t \/ (exists e', Step e e'))
           /\ (Step e e' -> (exists t', HasT e' t')).
Proof.
  intros.
  split.
  apply Progress.
  exact H.
  intros.
  apply Preservation with (e1 := e) (t1 := t); auto.
Qed.
