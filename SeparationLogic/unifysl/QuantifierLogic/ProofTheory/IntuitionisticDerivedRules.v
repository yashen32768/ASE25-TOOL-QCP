Require Import Logic.lib.Coqlib.
Require Import Logic.lib.SublistT.
Require Import Logic.GeneralLogic.Base.
Require Import Logic.MinimumLogic.Syntax.
Require Import Logic.PropositionalLogic.Syntax.
Require Import Logic.QuantifierLogic.Syntax.
Require Import Logic.MinimumLogic.ProofTheory.Minimum.
Require Import Logic.MinimumLogic.ProofTheory.RewriteClass.
Require Import Logic.PropositionalLogic.ProofTheory.Intuitionistic.
Require Import Logic.PropositionalLogic.ProofTheory.RewriteClass.
Require Import Logic.QuantifierLogic.ProofTheory.QuantifierLogic.

Local Open Scope logic_base.
Local Open Scope syntax.
Import PropositionalLanguageNotation.

Lemma allp_K
      (BL: BinderLanguage)
      {nBL: NormalBinderLanguage BL}
      {pBL: PropositionalBinderLanguage BL}
      {qL: QuantifierLanguage BL}
      (BGamma: BindedProofTheory BL)
      {nGamma: forall ts, NormalProofTheory (binded_L ts) (binded_Gamma ts)}
      {mpGamma: forall ts, MinimumPropositionalLogic (binded_L ts) (binded_Gamma ts)}
      {ipGamma: forall ts, IntuitionisticPropositionalLogic (binded_L ts) (binded_Gamma ts)}
      {qGamma: QuantifierLogic BL BGamma}:
  forall (t: type) (ts: list type) (x y: binded_expr (t :: ts)),
    |-- allp (x --> y) --> (allp x --> allp y).
Proof.
  intros.
  rewrite __provable_derivable.
  rewrite <- !derivables_impp_theorem.
  eapply derivables_modus_ponens.
  + apply derivables_andp_intros.
    - apply derivable_assum1.
    - apply deduction_weaken1.
      apply derivable_assum1.
  + apply derivables_weaken0.
    eapply allp_gen.
    rewrite lift_andp, !lift_allp.
    rewrite !(allp_elim _ _ _ var_term).
Abort.

Lemma allp_intros
      (BL: BinderLanguage)
      {nL: forall ts, NormalLanguage (binded_L ts)}
      {qL: QuantifierLanguage BL}
      (BGamma: BindedProofTheory BL)
      {nGamma: forall ts, NormalProofTheory (binded_L ts) (binded_Gamma ts)}
      {mpGamma: forall ts, MinimumPropositionalLogic (binded_L ts) (binded_Gamma ts)}
      {qGamma: QuantifierLogic BL BGamma}:
  forall (t: type) (ts: list type) (x: binded_expr ts) (y: binded_expr (t :: ts)),
    |-- allp (lift t x --> y) --> (x --> allp y).
Proof.
  intros.
Abort.
