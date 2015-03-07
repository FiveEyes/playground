Require Import Coq.Strings.String.
Open Scope string_scope.

Definition id := string.

Inductive ty : Type :=
  | TArrow : ty -> ty -> ty
  | TNat : ty.

Inductive tm : Type :=
  | tvar : id -> tm
  | tapp : tm -> tm -> tm
  | tabs : id -> ty -> tm -> tm
  | tnat : nat -> tm
  | tsucc : tm -> tm
  | tpred : tm -> tm
  | tmult : tm -> tm -> tm
  | tif0 : tm -> tm -> tm -> tm.

Inductive value : tm -> Prop :=
  | v_abs : forall x T t,
      value (tabs x T t)
  | v_nat : forall n,
      value (tnat n).

Reserved Notation "'[' x ':=' s ']' t" (at level 20).

Fixpoint subst (x:id) (s:tm) (t:tm) : tm :=
  match t with
  | tvar x' => 
      if string_dec x x' then s else t
  | tabs x' T t1 => 
      tabs x' T (if string_dec x x' then t1 else ([x:=s] t1)) 
  | tapp t1 t2 => 
      tapp ([x:=s] t1) ([x:=s] t2)
  | tnat n =>
      tnat n
  | tsucc t1 => tsucc ([x:=s] t1)
  | tpred t1 => tpred ([x:=s] t1)
  | tmult t1 t2 => tmult ([x:=s] t1) ([x:=s] t2)
  | tif0 t1 t2 t3 => 
      tif0 ([x:=s] t1) ([x:=s] t2) ([x:=s] t3)
  end

where "'[' x ':=' s ']' t" := (subst x s t).

Eval compute in ["s":=(tnat 1)] (tvar "s").

Reserved Notation "t1 '=>' t2" (at level 40).

Inductive step : tm -> tm -> Prop :=
  | ST_AppAbs : forall x T t12 v2,
         value v2 ->
         (tapp (tabs x T t12) v2) => [x:=v2]t12
  | ST_App1 : forall t1 t1' t2,
         t1 => t1' ->
         tapp t1 t2 => tapp t1' t2
  | ST_App2 : forall v1 t2 t2',
         value v1 ->
         t2 => t2' -> 
         tapp v1 t2 => tapp v1 t2'
  | ST_TSUCCN : forall n,
       (tsucc (tnat n)) => (tnat (S n))
  | ST_TSUCC : forall t1 t1',
       t1 => t1' -> (tsucc t1) => (tsucc t1')
  | ST_IfNZ : forall n t1 t2,
      (tif0 (tnat (S n)) t1 t2) => t1
  | ST_IfZ : forall t1 t2,
      (tif0 (tnat O) t1 t2) => t2
  | ST_If0 : forall t1 t1' t2 t3,
      t1 => t1' ->
      (tif0 t1 t2 t3) => (tif0 t1' t2 t3)

where "t1 '=>' t2" := (step t1 t2).

Eval compute in (tsucc (tnat O) => tnat (S O)).
