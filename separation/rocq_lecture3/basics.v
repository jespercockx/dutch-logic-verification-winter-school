From semtyping Require Import setup.

Section basics.
  Context {PROP : bi}.

  Lemma sep_exist A (P R : PROP) (Ψ : A → PROP) :
    P ∗ (∃ a, Ψ a) ∗ R -∗ ∃ a, R ∗ Ψ a ∗ P.
  Proof.
    iIntros "[HP [[%a HΨ] HR]]". iFrame.
  Qed.

  Lemma sep_logic_misc (P Q : PROP) (Ψ : Z → PROP) :
    (∀ x, P ∗ (True -∗ True) -∗ Q -∗ Ψ x) -∗
    (P ∗ Q) -∗
    Ψ 0.
  Proof.
    iIntros "H [HP HQ]".
    iApply ("H" with "[HP]"); auto with iFrame.
  Qed.
End basics.