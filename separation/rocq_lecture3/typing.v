From semtyping Require Import one_shot.

Implicit Types x : string.

(** * Syntactic types and typing judgment *)
Inductive ty :=
  | TUnit : ty
  | TInt : ty
  | TProd : ty → ty → ty
  | TArr : ty → ty → ty
  | TChan : action → ty → ty.

Reserved Notation "Γ ⊢ₜ e : A" (at level 74, e, A at next level).

Inductive typed : gmap string ty → expr → ty → Prop :=
  (** Variables *)
  | Var_typed Γ x A :
     Γ !! x = Some A →
     Γ ⊢ₜ x : A
  (** Base values *)
  | Unit_typed Γ :
     Γ ⊢ₜ #() : TUnit
  | Int_typed Γ (i : Z) :
     Γ ⊢ₜ #i : TInt
  (** Products *)
  | Pair_typed Γ1 Γ2 e1 e2 A1 A2 :
     Γ1 ##ₘ Γ2 →
     Γ1 ⊢ₜ e1 : A1 → Γ2 ⊢ₜ e2 : A2 →
     Γ1 ∪ Γ2 ⊢ₜ (e1,e2) : TProd A1 A2
  | LetPair_typed Γ1 Γ2 x1 x2 e1 e2 A1 A2 B :
     x1 ≠ x2 →
     Γ1 ##ₘ Γ2 →
     Γ1 ⊢ₜ e1 : TProd A1 A2 →
     <[x1:=A1]> (<[x2:=A2]> Γ2) ⊢ₜ e2 : B →
     Γ1 ∪ Γ2 ⊢ₜ (let: (x1, x2) := e1 in e2) : B
  (** Functions *)
  | Lam_typed Γ x e A1 A2 :
     <[x:=A1]> Γ ⊢ₜ e : A2 →
     Γ ⊢ₜ (λ: x, e) : TArr A1 A2
  | App_typed Γ1 Γ2 e1 e2 A1 A2 :
     Γ1 ##ₘ Γ2 →
     Γ1 ⊢ₜ e1 : TArr A1 A2 → Γ2 ⊢ₜ e2 : A1 →
     Γ1 ∪ Γ2 ⊢ₜ e1 e2 : A2
  (** Channels *)
  | New_typed Γ A :
     Γ ⊢ₜ new : TArr TUnit (TProd (TChan Send A) (TChan Recv A))
  | Send_typed Γ A :
     Γ ⊢ₜ send : TArr (TProd (TChan Send A) A) TUnit
  | Recv_typed Γ A :
     Γ ⊢ₜ recv : TArr (TChan Recv A) A
  | Fork_typed Γ e :
     Γ ⊢ₜ e : TUnit → Γ ⊢ₜ Fork e : TUnit
where "Γ ⊢ₜ e : A" := (typed Γ e A).

(** The subset of safe expressions: those that never get stuck *)
Definition safe (e : expr) := ∀ h es' e' h',
  rtc erased_step ([e], h) (es', h') →
  e' ∈ es' →
  is_Some (to_val e') ∨ reducible e' h'.

(** The lemma we aim to prove. We immediately [Abort], the actual lemma (with
proof) can be found at the bottom of the file. *)
Lemma type_safety e A : ∅ ⊢ₜ e : A → safe e.
Proof. Abort.

(** * Semantic types and semantic typing judgment *)
Section semtyp.
  Context `{!heapGS Σ, !chanG Σ}.
  Notation iProp := (iProp Σ).

  (** Semantic types are Iris predicates over values *)
  Definition sem_ty := val → iProp.

  (** We define the semantic type formers as combinators *)
  Definition SUnit : sem_ty := λ w, ⌜w = #()⌝%I.
  Definition SInt : sem_ty := λ w, (∃ n : Z, ⌜w = #n⌝)%I.
  Definition SProd (A1 A2 : sem_ty) : sem_ty := λ w,
    (∃ v1 v2, ⌜w = (v1, v2)%V⌝ ∗ A1 v1 ∗ A2 v2)%I.
  Definition SArr (A1 A2 : sem_ty) : sem_ty := λ w,
    (∀ v, A1 v -∗ WP w v {{ A2 }})%I.
  Definition SChan (a : action) (A : sem_ty) : sem_ty := λ w,
    is_chan w a A.

  (** The logical relation *)
  Fixpoint interp (A : ty) : sem_ty :=
    match A with
    | TUnit => SUnit
    | TInt => SInt
    | TProd A1 A2 => SProd (interp A1) (interp A2)
    | TArr A1 A2 => SArr (interp A1) (interp A2)
    | TChan a A => SChan a (interp A)
    end.

  (** Interpretation of contexts as substitutions (which are modelled as finite
  maps from strings to values) *)
  Definition interp_env (Γ : gmap string ty) (vs : gmap string val) : iProp :=
    [∗ map] x↦A ∈ Γ, ∃ v, ⌜ vs !! x = Some v ⌝ ∗ interp A v.

  Lemma interp_env_union Γ1 Γ2 vs :
    Γ1 ##ₘ Γ2 →
    interp_env (Γ1 ∪ Γ2) vs ⊣⊢ interp_env Γ1 vs ∗ interp_env Γ2 vs.
  Proof. apply big_sepM_union. Qed.

  (** The semantic typing judgment *)
  Definition sem_typed
      (Γ : gmap string ty) (e : expr) (A : ty) : iProp :=
    tc_opaque (□ ∀ vs, interp_env Γ vs -∗ WP subst_map vs e {{ w, interp A w }})%I.
  Notation "Γ ⊨ e : A" := (sem_typed Γ e A)
    (at level 74, e, A at next level).

  Global Instance sem_typed_persistent Γ e A : Persistent (sem_typed Γ e A).
  Proof. rewrite /sem_typed /=. apply _. Qed.

  Lemma App_sem_typed Γ1 Γ2 e1 e2 A1 A2 :
    Γ1 ##ₘ Γ2 →
    Γ1 ⊨ e1 : TArr A1 A2 -∗
    Γ2 ⊨ e2 : A1 -∗
    Γ1 ∪ Γ2 ⊨ e1 e2 : A2.
  Proof.
    iIntros "%Hdisj #He1 #He2 %vs !# HΓ /=".
    iDestruct (interp_env_union with "HΓ") as "[HΓ1 HΓ2]"; first done.
    wp_apply (wp_wand with "(He2 [$])") as "%w2 Hw2".
    wp_apply (wp_wand with "(He1 [$])") as "%w1 Hw1 /=".
    by iApply "Hw1".
  Qed.

  Lemma Var_sem_typed Γ (x : string) A :
    Γ !! x = Some A →
    ⊢ Γ ⊨ x : A.
  Proof.
    iIntros "%Hx !# %vs HΓ /=".
    iDestruct (big_sepM_lookup with "HΓ") as "(%v & -> & HA)"; first done.
    by wp_pures.
  Qed.

  Lemma Unit_sem_typed Γ :
    ⊢ Γ ⊨ #() : TUnit.
  Proof.
    iIntros "!# %vs HΓ". simpl. iApply wp_value. rewrite /SUnit /=. auto.
  Qed.

  Lemma Int_sem_typed Γ (i : Z) :
    ⊢ Γ ⊨ #i : TInt.
  Proof.
    iIntros "!# %vs HΓ". simpl. iApply wp_value. rewrite /SInt /=. auto.
  Qed.

  Lemma Pair_sem_typed Γ1 Γ2 e1 e2 A1 A2 :
    Γ1 ##ₘ Γ2 →
    Γ1 ⊨ e1 : A1 -∗
    Γ2 ⊨ e2 : A2 -∗
    Γ1 ∪ Γ2 ⊨ (e1,e2) : TProd A1 A2.
  Proof.
    iIntros "%Hdisj #He1 #He2 %vs !# HΓ /=".
    iDestruct (interp_env_union with "HΓ") as "[HΓ1 HΓ2]"; first done.
    wp_apply (wp_wand with "(He2 [$])") as "%w2 Hw2".
    wp_apply (wp_wand with "(He1 [$])") as "%w1 Hw1 /=".
    wp_pures. by iFrame.
  Qed.

  Lemma interp_env_insert Γ x vs v A :
    interp A v -∗
    interp_env Γ vs -∗
    interp_env (<[x:=A]> Γ) (<[x:=v]> vs).
  Proof.
    iIntros "Hv HΓ". rewrite -(insert_delete_eq Γ).
    iApply (big_sepM_insert_2 with "[Hv]").
    - iFrame. by rewrite lookup_insert_eq.
    - iDestruct (big_sepM_subseteq with "HΓ") as "HΓ"; first apply delete_subseteq. 
      iApply (big_sepM_mono with "HΓ").
      iIntros (y B [??]%lookup_delete_Some) "(%w & %Hy & Hw)".
      iFrame. by rewrite lookup_insert_ne.
  Qed.

  Lemma LetPair_sem_typed Γ1 Γ2 x1 x2 e1 e2 A1 A2 B :
    x1 ≠ x2 →
    Γ1 ##ₘ Γ2 →
    Γ1 ⊨ e1 : TProd A1 A2 -∗
    <[x1:=A1]> (<[x2:=A2]> Γ2) ⊨ e2 : B -∗
    Γ1 ∪ Γ2 ⊨ (let: (x1, x2) := e1 in e2) : B.
  Proof.
    iIntros "%Hx %Hdisj #He1 #He2 %vs !# HΓ /=".
    iDestruct (interp_env_union with "HΓ") as "[HΓ1 HΓ2]"; first done.
    wp_apply (wp_wand with "(He1 [$])") as "%w1 Hw1 /=".
    iDestruct "Hw1" as "(%v1 & %v2 & -> & Hv1 & Hv2)".
    iApply LetPair_wp; simpl.
    rewrite -subst_map_insert -delete_insert_ne // -subst_map_insert.
    iApply "He2". iApply (interp_env_insert with "Hv1").
    by iApply (interp_env_insert with "Hv2").
  Qed.

  Lemma Lam_sem_typed Γ x e A1 A2 :
    <[x:=A1]> Γ ⊨ e : A2 -∗
    Γ ⊨ (λ: x, e) : TArr A1 A2.
  Proof.
    iIntros "#He %vs !# HΓ /=". wp_pures.
    iIntros "!> %w Hw". wp_pures. rewrite -subst_map_insert.
    iApply "He". by iApply (interp_env_insert with "Hw").
  Qed.

  Lemma New_sem_typed Γ A :
    ⊢ Γ ⊨ new : TArr TUnit (TProd (TChan Send A) (TChan Recv A)).
  Proof.
    iIntros "%vs !# _ /=". wp_pures. iIntros "!> %w ->".
    wp_apply (new_spec with "[//]") as (c1 c2) "[$$]". done.
  Qed.

  Lemma Send_sem_typed Γ A :
    ⊢ Γ ⊨ send : TArr (TProd (TChan Send A) A) TUnit.
  Proof.
    iIntros "%vs !# _ /=". wp_pures. iIntros "!> %v (%c & %w & -> & Hc & Hw)".
    wp_apply (send_spec with "[$Hc $Hw]"); auto.
  Qed.

  Lemma Recv_sem_typed Γ A :
    ⊢ Γ ⊨ recv : TArr (TChan Recv A) A.
  Proof.
    iIntros "%vs !# _ /=". wp_pures. iIntros "!> %c Hc".
    wp_apply (recv_spec with "Hc") as (v) "$".
  Qed.

  Lemma Fork_sem_typed Γ e : 
    Γ ⊨ e : TUnit -∗
    Γ ⊨ Fork e : TUnit.
  Proof.
    iIntros "#He %vs !# HΓ /=". iApply (wp_fork with "[HΓ]").
    - iApply (wp_wand with "(He HΓ)"); auto.
    - auto.
  Qed.

  (** The fundamental theorem of logical relations *)
  Theorem fundamental Γ e A :
    (Γ ⊢ₜ e : A) → (⊢ Γ ⊨ e : A).
  Proof.
    induction 1; simpl.
    - by iApply Var_sem_typed.
    - iApply Unit_sem_typed.
    - iApply Int_sem_typed.
    - by iApply Pair_sem_typed.
    - by iApply LetPair_sem_typed.
    - by iApply Lam_sem_typed.
    - by iApply App_sem_typed.
    - by iApply New_sem_typed.
    - by iApply Send_sem_typed.
    - by iApply Recv_sem_typed.
    - by iApply Fork_sem_typed.
  Qed.

  (** A simple example showing that shows that more programs are semantically
  typed than syntactically typed. *)
  Lemma sem_typed_unsafe_pure Γ :
    ⊢ Γ ⊨ (if: #true then #13 else #13 #37) : TInt.
  Proof.
    iIntros "!#" (vs) "Hvs /=". wp_pures. rewrite /SInt. auto.
  Qed.
End semtyp.

(** Rocq requires us to redefine notations outside of sections *)
Notation "Γ ⊨ e : A" := (sem_typed Γ e A)
  (at level 74, e, A at next level).

(** The adequacy theorem, which follows from Iris's adequay theorem (modulo
some technicalities). *)
Lemma sem_adequacy `{!heapGpreS Σ, !chanG Σ} e :
  (∀ `{!heapGS Σ}, ∃ A, ⊢ ∅ ⊨ e : A) → safe e.
Proof.
  intros Hty B es' e' B'.
  apply (heap_adequacy Σ NotStuck e B (λ _, True)); iIntros "//= % _".
  specialize (Hty _) as [A Hty].
  iDestruct (Hty $! ∅) as "#He".
  rewrite subst_map_empty. iApply (wp_wand with "(He [])").
  { rewrite /interp_env. auto. }
  auto.
Qed.

(** And finally type safety *)
Lemma type_safety e A : ∅ ⊢ₜ e : A → safe e.
Proof.
  intros Hty. apply (sem_adequacy (Σ:=#[heapΣ; chanΣ]))=> ?.
  exists A. by apply fundamental.
Qed.

(** No assumptions, so we did not cheat! *)
Print Assumptions type_safety.
