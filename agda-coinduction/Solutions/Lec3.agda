{-# OPTIONS --allow-unsolved-metas --guardedness --sized-types --cubical -WnoUnsupportedIndexedMatch #-}

open import Data.Bool.Base using (Bool; true; false; not; _∧_; _∨_; if_then_else_)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Fin.Base using (Fin; zero; suc)
open import Data.List.Base using (List; []; _∷_)
open import Data.Maybe.Base using (Maybe; nothing; just)
open import Data.Nat.Base using (ℕ; zero; suc; _+_)
open import Data.Product.Base using (_×_; _,_; proj₁; proj₂)
open import Data.Sum.Base as Sum using (_⊎_; inj₁; inj₂; [_,_]; [_,_]′)
open import Data.Vec.Base using (Vec; []; _∷_)
open import Function.Base using (id; const; _∘_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong; cong₂; subst)
open import Relation.Binary.Definitions using (DecidableEquality)
open import Relation.Binary.PropositionalEquality.Properties using (module ≡-Reasoning)
open import Relation.Nullary using (¬_)
open import Relation.Nullary.Decidable using (Dec; yes; no; does)

module Lec3 where

open import Lec1
open import Lec2

module Delay where

  mutual
    data Delay (A : Set) : Set where
      now    : A → Delay A
      later  : Delay' A → Delay A

    record Delay' (A : Set) : Set where
      coinductive
      field force : Delay A
  open Delay' public

  variable d d₁ d₂ : A

  never : Delay A
  never = later (λ where .force → never)

  laters : ℕ → A → Delay A
  laters zero a = now a
  laters (suc n) a = later
    (λ where .force → laters n a)

  mutual
    iter : (A → A ⊎ B) → A → Delay B
    iter f x = iter' f (f x)

    iter' : (A → A ⊎ B) → A ⊎ B → Delay B
    iter' f (inj₁ y) = later (λ where .force → iter f y)
    iter' f (inj₂ z) = now z

  _>>=_ : Delay A → (A → Delay B) → Delay B
  now x >>= f = f x
  later d >>= f = later λ where
    .force → d .force >>= f

  infix 3 _⇓_
  data _⇓_ {A} : Delay A → A → Set where
    now : (x : A) → now x ⇓ x
    later : d .force ⇓ x → later d ⇓ x

  infix 5 _~_ _~'_
  mutual
    data _~_ {A} : Delay A → Delay A → Set where
      now    : (x : A)  → now    x  ~ now    x
      later  : x ~' y   → later  x  ~ later  y

    record _~'_ (x y : Delay' A) : Set where
      coinductive
      field
        force : x .force ~ y .force
  open _~'_ public

  refl~ : (x : Delay A) → x ~ x
  refl~ (now x) = now x
  refl~ (later x) = later λ where
    .force → refl~ (x .force)

  now->>=  : (x : A) (f : A → Delay B)
           → now x >>= f ~ f x
  now->>= x f = refl~ (f x)

  >>=-now : (d : Delay A) → d >>= now ~ d
  >>=-now (now x) = now x
  >>=-now (later x) = later λ where
    .force → >>=-now (x .force)

  >>=-assoc : (d : Delay A)
    → (f : A → Delay B) (g : B → Delay C)
    → (d >>= f) >>= g ~ d >>= λ x → (f x >>= g)
  >>=-assoc (now x) f g = refl~ (f x >>= g)
  >>=-assoc (later d) f g = later λ where
    .force → >>=-assoc (d .force) f g

module StreamProcessors where

  open Coinduction
  open Bisimulation

  mutual
    data SP (A B : Set) : Set where
      get  : (A → SP A B)  → SP A B
      put  : B → SP' A B   → SP A B

    record SP' (A B : Set) : Set where
      coinductive
      field force : SP A B
  open SP'


  run : SP A B → Stream A → Stream B
  run (get f) xs = run (f (xs .head)) (xs .tail)
  run (put y sp)  xs .head  = y
  run (put y sp)  xs .tail  = run (sp .force) xs


  mutual
    sums : SP ℕ ℕ
    sums = get λ n → sumN n 0

    sumN : ℕ → ℕ → SP ℕ ℕ
    sumN zero a = put a λ where .force → sums
    sumN (suc n) a = get λ k → sumN n (a + k)

  sums-test : List ℕ
  sums-test = take 10 (run sums nats)

  -- C-c C-n StreamProcessors.sums-test

  compose : SP A B → SP B C → SP A C
  compose (put y f)  (get g)    = compose (f .force) (g y)
  compose (get f)    p2         = get (λ x → compose (f x) p2)
  compose p1         (put z g)  = put z (λ where .force → compose p1 (g .force))

  compose-correct :
    (p1 : SP A B) (p2 : SP B C) (s : Stream A) →
    run (compose p1 p2) s ~ run p2 (run p1 s)
  compose-correct (get f) p2 s = compose-correct (f (s .head)) p2 (s .tail)
  compose-correct (put y f) (get g) s = compose-correct (f .force) (g y) s
  compose-correct (put y f) (put z g) s .head = refl
  compose-correct (put y f) (put z g) s .tail = compose-correct (put y f) (g .force) s



module FormalLanguages (A : Set) (_≟_ : DecidableEquality A) where

  open import Size
  variable i : Size

  record Lang (i : Size) : Set where
    coinductive
    field
      ν  : Bool
      δ  : {j : Size< i} → A → Lang j
  open Lang public


  _∋_ : Lang ∞ → List A → Bool
  l ∋ []        = l .ν
  l ∋ (x ∷ xs)  = l .δ x ∋ xs

  trie : (List A → Bool) → Lang i
  trie f .ν    = f []
  trie f .δ a  = trie (f ∘ (a ∷_))

  ∅ : Lang i
  ∅ .ν    = false
  ∅ .δ _  = ∅

  ε : Lang i
  ε .ν    = true
  ε .δ _  = ∅

  char : A → Lang i
  char a .ν    = false
  char a .δ b  = if does (a ≟ b) then ε else ∅

  complement : Lang i → Lang i
  complement l .ν    = not (l .ν)
  complement l .δ x  =
    complement (l .δ x)

  _∩_ : Lang i → Lang i → Lang i
  (l₁ ∩ l₂) .ν    = l₁ .ν ∧ l₂ .ν
  (l₁ ∩ l₂) .δ x  =
    l₁ .δ x ∩ l₂ .δ x

  _∪_ : Lang i → Lang i → Lang i
  (l₁ ∪ l₂) .ν    = l₁ .ν ∨ l₂ .ν
  (l₁ ∪ l₂) .δ x  = l₁ .δ x ∪ l₂ .δ x

  _·_ : Lang i → Lang i → Lang i
  (l₁ · l₂) .ν    = l₁ .ν ∧ l₂ .ν
  (l₁ · l₂) .δ x  = (if l₁ .ν then l₂ else ∅) ∪ (l₁ .δ x · l₂)

  _* : Lang i → Lang i
  (l *) .ν    = true
  (l *) .δ x  = l .δ x · (l *)

  infix 6 _~⟨_⟩~_
  record _~⟨_⟩~_
    (l₁ : Lang ∞) (i : Size) (l₂ : Lang ∞) : Set where
    coinductive
    field
      ν  : l₁ .ν ≡ l₂ .ν
      δ  : {j : Size< i} (x : A) → l₁ .δ x ~⟨ j ⟩~ l₂ .δ x
  open _~⟨_⟩~_

  arden : (k l m : Lang ∞) →
    l ~⟨ ∞ ⟩~ (k · l) ∪ m → l ~⟨ ∞ ⟩~ (k *) · m
  arden = {!   !}
