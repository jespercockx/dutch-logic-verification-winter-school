From iris.heap_lang Require Export metatheory adequacy proofmode notation.
From iris Require Export options.

Hint Extern 0 (_ ##ₘ _) => by apply map_disjoint_fmap : core.

(** HeapLang does not have a let-pair construct as primitive, which is common in
substructural type systems. We just encode it and prove the expected WP rule. *)
Definition pair_elim : val :=
  λ: "f" "x", "f" (Fst "x") (Snd "x").

Notation LetPair x1 x2 e1 e2 :=
  (pair_elim (Lam x1 (Lam x2 e2)) e1) (only parsing).

Notation "'let:' ( x1 , x2 ) := e1 'in' e2" :=
  (LetPair x1%binder x2%binder e1%E e2%E)
  (at level 200, x1, x2 at level 1, e1, e2 at level 200,
   format "'[' 'let:'  ( x1 , x2 )  :=  '[' e1 ']'  'in'  '/' e2 ']'") : expr_scope.

Lemma LetPair_wp `{heapGS Σ} (Φ : val → iProp Σ) x1 x2 v1 v2 e :
  WP (subst' x1 v1 (subst' x2 v2 e)) {{ Φ }} -∗
  WP (let: (x1, x2) := (v1, v2)%V in e) {{ Φ }}.
Proof.
  iIntros "Hwp". rewrite /pair_elim. wp_pures.
  destruct x1, x2; simpl; wp_pures; [by auto..|].
  case_decide as Hx.
  - by rewrite subst_subst_ne; last naive_solver.
  - apply not_and_r in Hx as [?%dec_stable|?%dec_stable]; simplify_eq/=.
    by rewrite subst_subst.
Qed.
