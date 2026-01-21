{-# OPTIONS --guardedness --sized-types --cubical-compatible -WnoUnsupportedIndexedMatch --allow-unsolved-metas #-}

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
open import Relation.Binary.PropositionalEquality.Properties using (module ≡-Reasoning)


variable
  A B C : Set
  x y z : A
  f g h : A → B
  k l m n : ℕ
  xs ys zs : A

module DataTypesAndPatternMatching where

  isEven : ℕ → Bool
  isEven n = {!   !}

  _*_ : ℕ → ℕ → ℕ
  m * n = {!   !}

  _≤_ : ℕ → ℕ → Bool
  m ≤ n = {!   !}

  map : (A → B) → List A → List B
  map f xs = {!   !}

  _++_ : List A → List A → List A
  xs ++ ys = {!   !}

module DependentTypes where

  zipVec : Vec A n → Vec B n → Vec (A × B) n
  zipVec xs ys = {!   !}

  updateVecAt : Fin n → A → Vec A n → Vec A n
  updateVecAt i x ys = {!   !}

module Coinduction where

  record Stream (A : Set) : Set where
    coinductive
    field
      head  : A
      tail  : Stream A
  open Stream public

  variable s s1 s2 : Stream A

  take : ℕ → Stream A → List A
  take zero s = []
  take (suc n) s = s .head ∷ take n (s .tail)

  drop : ℕ → Stream A → Stream A
  drop zero     s  = s
  drop (suc n)  s  = drop n (s .tail)

  map : (A → B) → Stream A → Stream B
  map f xs .head = f (xs .head)
  map f xs .tail = map f (xs .tail)

  _∷S_ : A → Stream A → Stream A
  (x ∷S xs) .head = x
  (x ∷S xs) .tail = xs

  _++_ : List A → Stream A → Stream A
  [] ++ ys = ys
  (x ∷ xs) ++ ys = x ∷S (xs ++ ys)

  natsFrom : ℕ → Stream ℕ
  natsFrom n .head = n
  natsFrom n .tail = natsFrom (suc n)

  nats : Stream ℕ
  nats = natsFrom 0

  repeat : A → Stream A
  repeat x = {!   !}

  lookup : Stream A → ℕ → A
  lookup xs n = {!   !}

  tabulate : (ℕ → A) → Stream A
  tabulate f = {!   !}

  fibonacci : Stream ℕ
  fibonacci = {!   !}

  transpose : Stream (Stream A) → Stream (Stream A)
  transpose xss = {!   !}

  transpose-flips-lookup : (xss : Stream (Stream A)) (i j : ℕ)
    → lookup (lookup (transpose xss) i) j ≡ lookup (lookup xss j) i
  transpose-flips-lookup xss i j = {!   !}


  mutual
    data Colist (A : Set) : Set where
      []   : Colist A
      _∷_  : A → Colist' A → Colist A

    record Colist' (A : Set) : Set where
      coinductive
      field
        force : Colist A
  open Colist' public

  fromStream : Stream A → Colist A
  fromStream {A} xs = xs .head ∷ (λ where .force → fromStream (xs .tail))

  fromList : List A → Colist A
  fromList xs = {!   !}

  mutual
    data Coℕ : Set where
      zero  : Coℕ
      suc   : Coℕ' → Coℕ

    record Coℕ' : Set where
      coinductive
      field force : Coℕ
  open Coℕ' public

  ∞ : Coℕ
  ∞ = {!   !}

  fromℕ : ℕ → Coℕ
  fromℕ n = {!   !}

  colength : Colist A → Coℕ
  colength xs = {!   !}


module SizedTypes where

  open import Size
  variable i : Size

  record Stream (A : Set) (i : Size) : Set where
    coinductive
    field
      head  : A
      tail  : {j : Size< i} → Stream A j
  open Stream

  take : ℕ → Stream A ∞ → List A
  take zero s     = []
  take (suc n) s  = s .head ∷ take n (s .tail)

  drop : ℕ → Stream A ∞ → Stream A ∞
  drop n s = {!   !}

  zeroes : Stream ℕ i
  zeroes .head  = 0
  zeroes .tail  = zeroes

  map : (A → B) → Stream A i → Stream B i
  map f xs .head = f (xs .head)
  map f xs .tail = map f (xs .tail)

  nats : Stream ℕ i
  nats .head = 0
  nats .tail = map suc nats

  zipWith : (A → B → C) → Stream A i → Stream B i → Stream C i
  zipWith f xs ys = {!   !}

  fibonacci : Stream ℕ i
  fibonacci = {!   !}
