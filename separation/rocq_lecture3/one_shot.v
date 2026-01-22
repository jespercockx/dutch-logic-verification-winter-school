From iris.base_logic.lib Require Import invariants token.
From semtyping Require Export setup.

(** This file contains the implementation and verification of the one-shot
channel. *) 
Definition new : val := λ: <>,
  let: "c" := ref NONE in ("c", "c").
Definition send : val := λ: "cv",
  Fst "cv" <- SOME (Snd "cv").
Definition recv : val :=
  rec: "go" "c" :=
    match: !"c" with
      NONE => "go" "c"
    | SOME "v" => Free "c";; "v"
    end.

Class chanG Σ := ChanG { #[local] chanG_tokenG :: tokenG Σ }.
Definition chanΣ : gFunctors := #[tokenΣ].
Global Instance chanG_chanΣ {Σ} : subG chanΣ Σ → chanG Σ.
Proof. solve_inG. Qed.

Inductive action := Send | Recv.

Section proof_base.
  Context `{!heapGS Σ, !chanG Σ}.
  Notation iProp := (iProp Σ).
  Let N := nroot .@ "chan".

  Definition chan_inv (γ1 γ2 : gname) (l : loc)
      (Φ : val → iProp) : iProp :=
    (l ↦ NONEV) ∨
    (∃ v, l ↦ SOMEV v ∗ token γ1 ∗ Φ v) ∨
    (token γ1 ∗ token γ2).
  Definition is_chan (c : val) (a : action) (Φ : val → iProp) : iProp :=
    ∃ γ1 γ2 (l : loc),
      ⌜c = #l⌝ ∗
      inv N (chan_inv γ1 γ2 l Φ) ∗
      token (if a is Send then γ1 else γ2).

  Lemma new_spec Φ :
    {{{ True }}}
      new #()
    {{{ c1 c2, RET (c1,c2); is_chan c1 Send Φ ∗ is_chan c2 Recv Φ }}}.
  Proof.
    iIntros (Ψ) "_ HΨ". wp_lam. wp_alloc l as "Hl". wp_pures.
    iApply "HΨ".
    iMod token_alloc as (γ1) "Hγ1".
    iMod token_alloc as (γ2) "Hγ2".
    iMod (inv_alloc N _ (chan_inv γ1 γ2 l Φ) with "[Hl]") as "#?"; [by iLeft|].
    iSplitL "Hγ1"; iFrame; eauto.
  Qed.

  Lemma send_spec c Φ v :
    {{{ is_chan c Send Φ ∗ Φ v }}} send (c, v)%V {{{ RET #(); True }}}.
  Proof.
    iIntros (φ) "[(%γ1 & %γ2 & %l & -> & #Hinv & Htok) HP] Hφ /=".
    wp_lam; wp_pures.
    iInv N as "[Hl|[(%w & Hl & >Htok' & HΦ')|>[Htok' Htok'']]]".
    - wp_store. iSplitR "Hφ"; last by iApply "Hφ".
      rewrite /chan_inv; eauto 10 with iFrame.
    - iCombine "Htok Htok'" gives %[].
    - iCombine "Htok Htok'" gives %[].
  Qed.

  Lemma recv_spec c Φ :
    {{{ is_chan c Recv Φ }}} recv c {{{ v, RET v; Φ v }}}.
  Proof.
    iIntros (φ) "(%γ1 & %γ2 & %l & -> & #Hinv & Htok) Hφ /=".
    iLöb as "IH". wp_rec. wp_bind (Load _).
    iInv N as "[Hl|[(%w & Hl & Htok' & HΦ')|>[Htok' Htok'']]]".
    - wp_load. iModIntro. iSplitL "Hl"; [iNext; by iLeft|].
      wp_match. iApply ("IH" with "Htok Hφ").
    - wp_load. iModIntro. iSplitL "Htok Htok'".
      + rewrite /chan_inv. by eauto with iFrame.
      + wp_match. wp_free. wp_seq. by iApply "Hφ".
    - iCombine "Htok Htok''" gives %[].
  Qed.
End proof_base.

Global Typeclasses Opaque is_chan.
