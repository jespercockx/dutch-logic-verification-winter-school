{-# OPTIONS --guardedness #-}

open import Data.Bool.Base using (Bool; true; false; not; _∧_; _∨_; if_then_else_)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.List.Base using (List; []; _∷_)
open import Data.Maybe.Base using (Maybe; nothing; just)
open import Data.Nat.Base using (ℕ; zero; suc; _+_)
open import Data.Sum.Base as Sum using (_⊎_; inj₁; inj₂; [_,_]; [_,_]′)
open import Function.Base using (id; const; _∘_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong; cong₂; subst)
open import Relation.Binary.PropositionalEquality.Properties using (module ≡-Reasoning)
open import Relation.Binary.Definitions using (DecidableEquality)
open import Relation.Nullary using (¬_)
open import Relation.Nullary.Decidable using (Dec; yes; no; does)

open import Coinduction

data ZigZag : ℕ → ℕ → Set
record ZigZag' (m n : ℕ) : Set

data ZigZag where
  leaf : ZigZag 0 0
  node : ZigZag' i j → ZigZag' k l → ZigZag (suc j) (suc k)

record ZigZag' m n where
  coinductive
  field force : ZigZag m n
open ZigZag' public

test₁ : ZigZag 1 2
test₁ = node (λ where .force → leaf) (λ where .force → test₁)

-- test₂ : ZigZag (suc (suc {!   !})) {!   !}
-- test₂ = node (λ where .force → test₂) (λ where .force → test₂)
-- Failed to solve the following constraints:
--   suc (suc ?0) = ?0 : ℕ (blocked on _n_20)

test₃ : ZigZag 3 2
test₄ : ZigZag 1 4
test₃ = node (λ where .force → test₃) (λ where .force → test₄)
test₄ = node (λ where .force → leaf) (λ where .force → test₃)

zigs : ZigZag i j → ℕ
zags : ZigZag i j → ℕ

zigs leaf = 0
zigs (node l r) = suc (zags (l .force))
zags leaf = 0
zags (node l r) = suc (zigs (r .force))


record InfNot (b : Bool) : Set where
  coinductive
  constructor nons
  field
    force : InfNot (not b)
open InfNot

inftrue : InfNot true
inffalse : InfNot false

inftrue .force = inffalse
inffalse .force = inftrue


-- Infinite binary sequences where we forbid infinite consecutive ones.
data ZeroOne : ℕ → Set
record ZeroOne' (n : ℕ) : Set

data ZeroOne where
  Zero : ZeroOne' i → ZeroOne 0
  One  : ZeroOne' i → ZeroOne (suc i)

record ZeroOne' n where
  coinductive
  field force : ZeroOne n
open ZeroOne' public

allZeros : ZeroOne 0
allZeros = Zero λ where .force → allZeros

allOnes : ZeroOne {!   !}
allOnes = One λ where .force → allOnes

alternate01 : ZeroOne 0
alternate01 = Zero (λ where .force → One (λ where .force → alternate01))

