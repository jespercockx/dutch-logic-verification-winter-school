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

  zip : Vec A n → Vec B n → Vec (A × B) n
  zip [] [] = []
  zip (x ∷ xs) (y ∷ ys) = (x , y) ∷ zip xs ys

  updateVecAt : Fin n → A → Vec A n → Vec A n
  updateVecAt zero x (y ∷ ys) = x ∷ ys
  updateVecAt (suc i) x (y ∷ ys) = y ∷ updateVecAt i x ys

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

  maps : (A → B) → Stream A → Stream B
  maps f xs .head = f (xs .head)
  maps f xs .tail = maps f (xs .tail)

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
  repeat x .head = x
  repeat x .tail = repeat x

  lookup : Stream A → ℕ → A
  lookup xs zero = xs .head
  lookup xs (suc n) = lookup (xs .tail) n

  tabulate : (ℕ → A) → Stream A
  tabulate f .head = f 0
  tabulate f .tail = tabulate (f ∘ suc)

  fibonacci : Stream ℕ
  fibonacci = tabulate fib
    where
      fib : ℕ → ℕ
      fib zero = 1
      fib (suc zero) = 1
      fib (suc (suc x)) = fib x + fib (suc x)

  transpose : Stream (Stream A) → Stream (Stream A)
  transpose xss .head = maps head xss
  transpose xss .tail = transpose (maps tail xss)

  lookup-maps : (i : ℕ) → lookup (maps f s) i ≡ f (lookup s i)
  lookup-maps zero = refl
  lookup-maps (suc i) = lookup-maps i

  transpose-flips-lookup : (xss : Stream (Stream A)) (i j : ℕ)
                        → lookup (lookup (transpose xss) i) j ≡ lookup (lookup xss j) i
  transpose-flips-lookup xss zero j = lookup-maps j
  transpose-flips-lookup xss (suc i) j =
    begin
      lookup (lookup (transpose xss) (suc i)) j
    ≡⟨⟩
      lookup (lookup (transpose xss .tail) i) j
    ≡⟨ transpose-flips-lookup (maps tail xss) i j ⟩
      lookup (lookup (maps (λ r → tail r) xss) j) i
    ≡⟨ cong (λ yss → lookup yss i) (lookup-maps j) ⟩
      lookup (tail (lookup xss j)) i
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
  fromStream {A} xs = xs .head ∷ (λ where .force → fromStream (xs .tail))

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
      head  : A
      tail  : {j : Size< i} → Stream A j
  open Stream

  take : ℕ → Stream A ∞ → List A
  take zero s     = []
  take (suc n) s  = s .head ∷ take n (s .tail)

  drop : ℕ → Stream A ∞ → Stream A ∞
  drop zero s = s
  drop (suc n) s = drop n (s .tail)

  zeroes : Stream ℕ i
  zeroes .head  = 0
  zeroes .tail  = zeroes

  maps : (A → B) → Stream A i → Stream B i
  maps f xs .head = f (xs .head)
  maps f xs .tail = maps f (xs .tail)

  nats : Stream ℕ i
  nats .head = 0
  nats .tail = maps suc nats

  zipWith : (A → B → C) → Stream A i → Stream B i → Stream C i
  zipWith f xs ys .head = f (xs .head) (ys .head)
  zipWith f xs ys .tail = zipWith f (xs .tail) (ys .tail)

  fibonacci : Stream ℕ i
  fibonacci .head = 1
  fibonacci .tail .head = 1
  fibonacci .tail .tail = zipWith _+_ fibonacci (fibonacci .tail)
