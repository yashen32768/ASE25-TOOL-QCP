Require Import ZArith.

Module NaiveLang.
  Definition expr := (nat -> option Z) -> Prop.
  Definition context := expr -> Prop.
  Definition impp (e1 e2 : expr) : expr := fun st => e1 st -> e2 st.
  Definition andp (e1 e2 : expr) : expr := fun st => e1 st /\ e2 st.
  Definition orp  (e1 e2 : expr) : expr := fun st => e1 st \/ e2 st.
  Definition falsep : expr := fun st => False.
  Definition coq_prop (P: Prop): expr := fun _ => P.

  Definition join : (nat -> option Z) -> (nat -> option Z) -> (nat -> option Z) -> Prop :=
    fun x y z =>
      forall p: nat,
       (exists v, x p = Some v /\ y p = None /\ z p = Some v) \/
       (exists v, x p = None /\ y p = Some v /\ z p = Some v) \/
       (x p = None /\ y p = None /\ z p = None).
  Definition sepcon (e1 e2 : expr) : expr := fun st =>
    exists st1 st2, join st1 st2 st /\ e1 st1 /\ e2 st2.
  Definition emp : expr := fun st =>
    forall p, st p = None.
  Definition corable (e: expr): Prop := forall s1 s2, e s1 <-> e s2.
  
  Definition provable (e : expr) : Prop := forall st, e st.
End NaiveLang.

Require Import interface_4.

Module NaiveRule.
  Include DerivedNames (NaiveLang).
  Lemma provables_modus_ponens :
    forall x y : expr, provable (impp x y) -> provable x -> provable y.
  Proof. unfold provable, impp. auto. Qed.

  Lemma provable_axiom1 : forall x y : expr, provable (impp x (impp y x)).
  Proof. unfold provable, impp. auto. Qed.

  Lemma provable_axiom2 : forall x y z : expr,
      provable (impp (impp x (impp y z)) (impp (impp x y) (impp x z))).
  Proof. unfold provable, impp. auto. Qed.

  Lemma provable_andp_intros :
    forall x y : expr, provable (impp x (impp y (andp x y))).
  Proof. unfold provable, impp, andp. auto. Qed.

  Lemma provable_andp_elim1 : forall x y : expr, provable (impp (andp x y) x).
  Proof. unfold provable, impp, andp. tauto. Qed.

  Lemma provable_andp_elim2 : forall x y : expr, provable (impp (andp x y) y).
  Proof. unfold provable, impp, andp. tauto. Qed.

  Lemma provable_orp_intros1 : forall x y : expr, provable (impp x (orp x y)).
  Proof. unfold provable, impp, orp. auto. Qed.

  Lemma provable_orp_intros2 : forall x y : expr, provable (impp y (orp x y)).
  Proof. unfold provable, impp, orp. auto. Qed.

  Lemma provable_orp_elim : forall x y z : expr,
      provable (impp (impp x z) (impp (impp y z) (impp (orp x y) z))).
  Proof. unfold provable, impp, orp. tauto. Qed.

  Lemma provable_falsep_elim : forall x : expr, provable (impp falsep x).
  Proof. unfold provable, impp, falsep. destruct 1. Qed.

  Lemma provable_peirce_law : forall x y: expr, provable (impp (impp (impp x y) x) x).
  Proof. unfold provable, impp. intros; tauto. Qed.

  Axiom provable_sepcon_impp_comm: forall x y, provable (iffp (sepcon x y) (sepcon y x)).
  Axiom provable_sepcon_assoc: forall x y z,
      provable (iffp (sepcon x (sepcon y z)) (sepcon (sepcon x y) z)).
  Axiom provable_sepcon_mono : (forall x1 x2 y1 y2 : expr, provable (impp x1 x2) -> provable (impp y1 y2) -> provable (impp (sepcon x1 y1) (sepcon x2 y2))) .
  Axiom provable_sepcon_emp : (forall x : expr, provable (iffp (sepcon x emp) x)) .
  Axiom provable_falsep_sepcon_derives : (forall x : expr, provable (impp (sepcon falsep x) falsep)) .
  Axiom provable_orp_sepcon_derives : (forall x y z : expr, provable (impp (sepcon (orp x y) z) (orp (sepcon x z) (sepcon y z)))) .
  Axiom corable_coq_prop : (forall P : Prop, corable (coq_prop P)) .
  Axiom corable_preserved' : (forall x y : expr, provable (iffp x y) -> corable x -> corable y) .
  Axiom corable_andp_sepcon1 : (forall x y z : expr, corable x -> provable (iffp (sepcon (andp x y) z) (andp x (sepcon y z)))) .
End NaiveRule.

Module T := LogicTheorem NaiveLang NaiveRule.
Module Solver := IPSolver NaiveLang.
Import T.
Import Solver.

