module Avl where

open import Data.Nat using (ℕ; zero; suc; _+_; _*_; _≤_; z≤n; s≤s)
open import Data.List using (List; []; _∷_; length)

import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; sym; trans; cong; subst; resp)
open Eq.≡-Reasoning using (begin_; _≡⟨⟩_; step-≡; _∎)
open import Axiom.Extensionality.Propositional using (Extensionality)

postulate
  fun-ext : ∀ {a b} → Extensionality a b

_<_ : ℕ → ℕ → Set
n < m = suc n ≤ m

_>_ : ℕ → ℕ → Set
n > m = m < n

infix 4 _<_
infix 4 _>_

--interval : ℕ → ℕ → ℕ → Set
--interval x min max = {!   !}

data ℕ∞ : Set where
  -∞  :     ℕ∞
  [_] : ℕ → ℕ∞
  +∞  :     ℕ∞

data _<∞_ : ℕ∞ → ℕ∞ → Set where
  -∞<n  : {n   : ℕ∞}  →          -∞   <∞   n
  []<[] : {n m : ℕ}   → n < m → [ n ] <∞ [ m ]
  n<+∞  : {n   : ℕ∞}  →           n   <∞  +∞

max : ℕ → ℕ → ℕ
max zero b = b
max (suc a) zero = suc a
max (suc a) (suc b) = suc (max a b)

data Avl (A : Set) (lower upper : ℕ∞) : Set where
  empty : (p : lower <∞ upper) → Avl A lower upper
  node : (n : ℕ)
            → Avl A lower [ n ]
            → Avl A [ n ] upper
            → Avl A lower upper

test : Avl ℕ -∞ +∞
test = node 7 (node 5 (empty -∞<n) (empty ([]<[] (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s z≤n))))))))) (empty n<+∞)


  