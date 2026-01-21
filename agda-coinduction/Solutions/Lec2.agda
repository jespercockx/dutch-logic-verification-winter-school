{-# OPTIONS --guardedness --sized-types --cubical -WnoUnsupportedIndexedMatch #-}


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
open import Relation.Nullary using (¬_)

open import Lec1
open DataTypesAndPatternMatching

module Lec2 where


module CurryHoward where

  not-not-lem : ¬ ¬ (A ⊎ ¬ A)
  not-not-lem f = f (inj₂ (λ a → f (inj₁ a)))

module FiniteInfinite where

  open Coinduction

  data Finite {A : Set} : Colist A → Set where
    []  : Finite []
    -∷_ : Finite (xs .force) → Finite (x ∷ xs)

  fromListFin : (xs : List A) → Finite (fromList xs)
  fromListFin [] = []
  fromListFin (x ∷ xs) = -∷ fromListFin xs

  toList : (xs : Colist A) → Finite xs → List A
  toList []        []        = []
  toList (x ∷ xs)  (-∷ fin)  = x ∷ toList (xs .force) fin


  mutual
    data Infinite {A : Set} : Colist A → Set where
      -∷_ : Infinite' xs → Infinite (x ∷ xs)

    record Infinite' (xs : Colist' A) : Set where
      coinductive
      field force : Infinite (xs .force)
  open Infinite' public

  fromStreamInf : (xs : Stream A) → Infinite (fromStream xs)
  fromStreamInf xs = -∷ λ where .force → fromStreamInf (xs .tail)

  toStream : (xs : Colist A) → Infinite xs → Stream A
  toStream (x ∷ xs) (-∷ inf) .head = x
  toStream (x ∷ xs) (-∷ inf) .tail = toStream (xs .force) (inf .force)

  infinite-not-finite : Infinite xs → ¬ (Finite xs)
  infinite-not-finite ()       []
  infinite-not-finite (-∷ inf) (-∷ fin) = infinite-not-finite (inf .force) fin

  not-finite-infinite : ¬ (Finite xs) → Infinite xs
  not-finite-infinite {xs = []} not-finite = ⊥-elim (not-finite [])
  not-finite-infinite {xs = x ∷ xs} not-finite = -∷ (λ where .force → not-finite-infinite (not-finite ∘ -∷_))

  fromListInv : (xs : List A) → toList (fromList xs) (fromListFin xs) ≡ xs
  fromListInv [] = refl
  fromListInv (x ∷ xs) = cong (x ∷_) (fromListInv xs)


module EquationalReasoning where

  open ≡-Reasoning

  append-[] : (xs : List A) → xs ++ [] ≡ xs
  append-[] [] = refl
  append-[] (x ∷ xs) = cong (x ∷_) (append-[] xs)

  append-assoc : (xs ys zs : List A) → (xs ++ ys) ++ zs ≡ xs ++ (ys ++ zs)
  append-assoc [] ys zs = refl
  append-assoc (x ∷ xs) ys zs = cong (x ∷_) (append-assoc xs ys zs)

  list-functor-comp : {A B C : Set} →
    (f : B → C) (g : A → B) (xs : List A) →
    map (f ∘ g) xs ≡ (map f ∘ map g) xs

  list-functor-comp f g [] =
    map (f ∘ g) []      ≡⟨⟩
    []                  ≡⟨⟩
    (map f ∘ map g) []  ∎

  list-functor-comp f g (x ∷ xs) =
    map (f ∘ g) (x ∷ xs)      ≡⟨⟩
    f (g x) ∷ map (f ∘ g) xs  ≡⟨ cong (f (g x) ∷_) (list-functor-comp f g xs) ⟩
    (map f ∘ map g) (x ∷ xs)  ∎

  reverse : List A → List A
  reverse []        = []
  reverse (x ∷ xs)  = reverse xs ++ (x ∷ [])

  reverse-acc : List A → List A → List A
  reverse-acc []        ys = ys
  reverse-acc (x ∷ xs) ys = reverse-acc xs (x ∷ ys)

  reverse' : List A → List A
  reverse' xs = reverse-acc xs []

  reverse-acc-lemma : (xs ys : List A)
    → reverse-acc xs ys ≡ reverse xs ++ ys
  reverse-acc-lemma [] ys = refl
  reverse-acc-lemma (x ∷ xs) ys =
    reverse-acc (x ∷ xs) ys         ≡⟨⟩
    reverse-acc xs (x ∷ ys)         ≡⟨ reverse-acc-lemma xs (x ∷ ys) ⟩
    reverse xs ++ (x ∷ ys)          ≡⟨ sym (append-assoc (reverse xs) (x ∷ []) ys) ⟩
    (reverse xs ++ (x ∷ [])) ++ ys  ≡⟨⟩
    reverse (x ∷ xs) ++ ys          ∎

  reverse'-reverse : (xs : List A) → reverse' xs ≡ reverse xs
  reverse'-reverse xs =
    reverse' xs         ≡⟨⟩
    reverse-acc xs []   ≡⟨ reverse-acc-lemma xs [] ⟩
    reverse xs ++ []    ≡⟨ append-[] (reverse xs) ⟩
    reverse xs          ∎


module Bisimulation where

  open Coinduction
  open FiniteInfinite

  record _~_ {A : Set} (s1 s2 : Stream A) : Set where
    coinductive
    field
      head  :  s1  .head  ≡  s2  .head
      tail  :  s1  .tail  ~  s2  .tail
  open _~_ public

  refl~ : (s : Stream A) → s ~ s
  refl~ s .head = refl
  refl~ s .tail = refl~ (s .tail)

  fromStreamInv : (xs : Stream A)
    → toStream (fromStream xs) (fromStreamInf xs) ~ xs
  fromStreamInv xs .head = refl
  fromStreamInv xs .tail = fromStreamInv (xs .tail)

module CubicalBisimulation where

  open Coinduction
  open Bisimulation
  open import Agda.Primitive.Cubical using (I; i0; i1; PathP)

  Path : (A : Set) → A → A → Set
  Path A x y = PathP (λ _ → A) x y

  reflP : Path A x x
  reflP {x = x} i = x

  ≡-to-Path : x ≡ y → Path A x y
  ≡-to-Path refl = reflP

  ~-to-Path : xs ~ ys → Path (Stream A) xs ys
  ~-to-Path bisim i .head = ≡-to-Path (bisim .head) i
  ~-to-Path bisim i .tail = ~-to-Path (bisim .tail) i

