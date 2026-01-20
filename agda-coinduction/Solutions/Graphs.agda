{-# OPTIONS --guardedness #-}

open import Data.Bool.Base using (Bool; true; false; not; _∧_; _∨_; if_then_else_)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.List.Base using (List; []; _∷_; _++_; map; concatMap)
open import Data.Maybe.Base using (Maybe; nothing; just)
open import Data.Nat.Base using (ℕ; zero; suc; _+_)
open import Data.Product.Base using (Σ; _×_; _,_; proj₁; proj₂)
open import Data.Sum.Base as Sum using (_⊎_; inj₁; inj₂; [_,_]; [_,_]′)
open import Data.Unit.Base using (⊤; tt)
open import Function.Base using (id; const; _∘_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong; cong₂; subst)
open import Relation.Binary.PropositionalEquality.Properties using (module ≡-Reasoning)
open import Relation.Binary.Definitions using (DecidableEquality)
open import Relation.Nullary using (¬_)
open import Relation.Nullary.Decidable using (Dec; yes; no; does)

open import Coinduction

-- To simplify things a bit compared to the paper, we use a simple list for the neighbours.
Neighbours : Set → Set
Neighbours = List

-- A graph with node set V is a map from nodes to their neighbours.
GraphOf : Set → Set
GraphOf V = V → Neighbours V

-- Empty graph
empty : GraphOf A
empty _ = []

-- Overlay of two graphs
_⊞_  : GraphOf A → GraphOf A → GraphOf A
f ⊞ g = λ x → f x ++ g x

-- Graph with only self-loops
return : GraphOf A
return = λ x → x ∷ []

-- Composition of two graphs
_>=>_ : GraphOf A → GraphOf A → GraphOf A
f >=> g = λ x → concatMap g (f x)

-- Transitive closure of the graph
pathed : GraphOf A → GraphOf (A × List A)
pathed g = λ (x , xs) → map (λ t → t , x ∷ xs) (g x)

-- A graph with self-loops for nodes that satisfy p
filtering : (A → Bool) → GraphOf A
filtering p = λ x → if p x then x ∷ [] else []

Graph : Set₁
Graph = Σ Set GraphOf

unit : Graph
unit = ⊤ , return

void : Graph
void = ⊥ , ⊥-elim

_***_ : GraphOf A → GraphOf B → GraphOf (A × B)
f *** g = λ (x , y) → {! concatMap (  !}

_* : GraphOf A → GraphOf A
g * = {!   !}
