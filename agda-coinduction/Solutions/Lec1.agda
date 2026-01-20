{-# OPTIONS --guardedness --sized-types --cubical-compatible -WnoUnsupportedIndexedMatch #-}

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

module Lec1 where

variable
  A B C : Set
  x y z : A
  f g h : A → B
  k l m n : ℕ
  xs ys zs : A

module DataTypesAndPatternMatching where

  isEven : ℕ → Bool
  isEven zero = true
  isEven (suc zero) = false
  isEven (suc (suc n)) = isEven n

  _*_ : ℕ → ℕ → ℕ
  zero * n = zero
  suc m * n = m * n + n

  _≤_ : ℕ → ℕ → Bool
  zero ≤ n = true
  suc m ≤ zero = false
  suc m ≤ suc n = m ≤ n

  map : (A → B) → List A → List B
  map f [] = []
  map f (x ∷ xs) = f x ∷ map f xs

  _++_ : List A → List A → List A
  [] ++ ys = ys
  (x ∷ xs) ++ ys = x ∷ (xs ++ ys)

module DependentTypes where

  zipVec : Vec A n → Vec B n → Vec (A × B) n
  zipVec [] [] = []
  zipVec (x ∷ xs) (y ∷ ys) = (x , y) ∷ zipVec xs ys

  updateVecAt : Fin n → A → Vec A n → Vec A n
  updateVecAt zero x (y ∷ ys) = x ∷ ys
  updateVecAt (suc i) x (y ∷ ys) = y ∷ updateVecAt i x ys

module Coinduction where

  record Stream (A : Set) : Set where
    coinductive
    field
      headS  : A
      tailS  : Stream A
  open Stream public

  variable s s1 s2 : Stream A

  takeS : ℕ → Stream A → List A
  takeS zero s = []
  takeS (suc n) s = s .headS ∷ takeS n (s .tailS)

  dropS : ℕ → Stream A → Stream A
  dropS zero     s  = s
  dropS (suc n)  s  = dropS n (s .tailS)

  mapS : (A → B) → Stream A → Stream B
  mapS f xs .headS = f (xs .headS)
  mapS f xs .tailS = mapS f (xs .tailS)

  _∷S_ : A → Stream A → Stream A
  (x ∷S xs) .headS = x
  (x ∷S xs) .tailS = xs

  _++S_ : List A → Stream A → Stream A
  [] ++S ys = ys
  (x ∷ xs) ++S ys = x ∷S (xs ++S ys)

  natsFrom : ℕ → Stream ℕ
  natsFrom n .headS = n
  natsFrom n .tailS = natsFrom (suc n)

  nats : Stream ℕ
  nats = natsFrom 0

  repeat : A → Stream A
  repeat x .headS = x
  repeat x .tailS = repeat x

  lookup : Stream A → ℕ → A
  lookup xs zero = xs .headS
  lookup xs (suc n) = lookup (xs .tailS) n

  tabulate : (ℕ → A) → Stream A
  tabulate f .headS = f 0
  tabulate f .tailS = tabulate (f ∘ suc)

  fibonacci : Stream ℕ
  fibonacci = tabulate fib
    where
      fib : ℕ → ℕ
      fib zero = 1
      fib (suc zero) = 1
      fib (suc (suc x)) = fib x + fib (suc x)

  transpose : Stream (Stream A) → Stream (Stream A)
  transpose xss .headS = mapS headS xss
  transpose xss .tailS = transpose (mapS tailS xss)

  lookup-mapS : (i : ℕ) → lookup (mapS f s) i ≡ f (lookup s i)
  lookup-mapS zero = refl
  lookup-mapS (suc i) = lookup-mapS i

  transpose-flips-lookup : (xss : Stream (Stream A)) (i j : ℕ)
                        → lookup (lookup (transpose xss) i) j ≡ lookup (lookup xss j) i
  transpose-flips-lookup xss zero j = lookup-mapS j
  transpose-flips-lookup xss (suc i) j =
    begin
      lookup (lookup (transpose xss) (suc i)) j
    ≡⟨⟩
      lookup (lookup (transpose xss .tailS) i) j
    ≡⟨ transpose-flips-lookup (mapS tailS xss) i j ⟩
      lookup (lookup (mapS (λ r → tailS r) xss) j) i
    ≡⟨ cong (λ yss → lookup yss i) (lookup-mapS j) ⟩
      lookup (tailS (lookup xss j)) i
    ≡⟨⟩
      lookup (lookup xss j) (suc i)
    ∎
    where open ≡-Reasoning


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
  fromStream {A} xs = xs .headS ∷ (λ where .force → fromStream (xs .tailS))

  fromList : List A → Colist A
  fromList [] = []
  fromList (x ∷ xs) = x ∷ λ where .force → fromList xs

  mutual
    data Coℕ : Set where
      zero  : Coℕ
      suc   : Coℕ' → Coℕ

    record Coℕ' : Set where
      coinductive
      field force : Coℕ
  open Coℕ' public

  ∞ : Coℕ
  ∞ = suc λ where .force → ∞

  fromℕ : ℕ → Coℕ
  fromℕ zero = zero
  fromℕ (suc n) = suc λ where .force → fromℕ n

  colength : Colist A → Coℕ
  colength [] = zero
  colength (x ∷ xs) = suc (λ where .force → colength (xs .force))


module SizedTypes where

  open import Size
  variable i : Size

  record Stream (A : Set) (i : Size) : Set where
    coinductive
    field
      headS  : A
      tailS  : {j : Size< i} → Stream A j
  open Stream

  takeS : ℕ → Stream A ∞ → List A
  takeS zero s     = []
  takeS (suc n) s  = s .headS ∷ takeS n (s .tailS)

  dropS : ℕ → Stream A ∞ → Stream A ∞
  dropS zero s = s
  dropS (suc n) s = dropS n (s .tailS)

  zeroes : Stream ℕ i
  zeroes .headS  = 0
  zeroes .tailS  = zeroes

  mapS : (A → B) → Stream A i → Stream B i
  mapS f xs .headS = f (xs .headS)
  mapS f xs .tailS = mapS f (xs .tailS)

  nats : Stream ℕ i
  nats .headS = 0
  nats .tailS = mapS suc nats

  zipWithS : (A → B → C) → Stream A i → Stream B i → Stream C i
  zipWithS f xs ys .headS = f (xs .headS) (ys .headS)
  zipWithS f xs ys .tailS = zipWithS f (xs .tailS) (ys .tailS)

  fibonacci : Stream ℕ i
  fibonacci .headS = 1
  fibonacci .tailS .headS = 1
  fibonacci .tailS .tailS = zipWithS _+_ fibonacci (fibonacci .tailS)
