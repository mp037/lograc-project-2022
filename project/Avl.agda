module Avl where

open import Agda.Builtin.Nat using () renaming (_-_ to _-ᴺ_)
open import Data.Nat using (ℕ; zero; suc; _+_; _*_; _≤_; _≤ᵇ_; z≤n; s≤s; _⊔_) renaming (∣_-_∣ to _-_)
open import Data.Nat.Properties using (≤-trans; ≤-reflexive; +-∸-assoc; +-comm; m∸n+n≡m; m≤n⇒m⊔n≡n; n≤1+n)
open import Data.List using (List; []; _∷_; length)
open import Data.Bool.Base using (T; if_then_else_)
open import Agda.Builtin.Bool public
open import Data.Maybe

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


data ℕ∞ : Set where
  -∞  :     ℕ∞
  [_] : ℕ → ℕ∞
  +∞  :     ℕ∞

data _<∞_ : ℕ∞ → ℕ∞ → Set where
  -∞<n  : {n   : ℕ∞}  →          -∞   <∞   n
  []<[] : {n m : ℕ}   → n < m → [ n ] <∞ [ m ]
  n<+∞  : {n   : ℕ∞}  →           n   <∞  +∞


data Avl (A : Set) (lower upper : ℕ∞) : ℕ → Set where --the last element is the height of the tree
  empty : (p : lower <∞ upper) → Avl A lower upper zero
  node : {l r : ℕ} → (n : ℕ)
            → Avl A lower [ n ] l
            → Avl A [ n ] upper r
            → (r - l) ≤ 1
            → Avl A lower upper ((l ⊔ r) + 1)


test : Avl ℕ -∞ +∞ 1
test = node 5 (empty -∞<n) (empty n<+∞) z≤n

test2 : Avl ℕ -∞ +∞ 2
test2 = node 5 (node 3 (empty -∞<n) (empty ([]<[] (s≤s (s≤s (s≤s (s≤s z≤n)))))) z≤n) 
               (empty n<+∞) (s≤s z≤n)

test3 : Avl ℕ -∞ +∞ 2
test3 = node 5 (node 3 (empty -∞<n) (empty ([]<[] (s≤s (s≤s (s≤s (s≤s z≤n)))))) z≤n) 
               (node 6 (empty ([]<[] (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s z≤n)))))))) (empty n<+∞) z≤n) z≤n

test4 : Avl ℕ -∞ +∞ 2
test4 = node 5 (empty -∞<n) 
               (node 6 (empty ([]<[] (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s z≤n)))))))) (empty n<+∞) z≤n) (s≤s z≤n)

data _∈_ (n : ℕ) : {lower upper : ℕ∞} {h : ℕ} → Avl ℕ lower upper h → Set where
  here : ∀ {ll rr hl hr} → {l : Avl ℕ ll [ n ] hl} {r : Avl ℕ [ n ] rr hr} {p : (hr - hl) ≤ 1} → n ∈ node n l r p
  left : ∀ {ll rr hl hr x} → {l : Avl ℕ ll [ x ] hl} {r : Avl ℕ [ x ] rr hr} {p : (hr - hl) ≤ 1} → n ∈ l → n ∈ node x l r p
  right : ∀ {ll rr hl hr x} → {l : Avl ℕ ll [ x ] hl} {r : Avl ℕ [ x ] rr hr} {p : (hr - hl) ≤ 1} → n ∈ r → n ∈ node x l r p

3∈test3 : 3 ∈ test3
3∈test3 = left here

5∈test3 : 5 ∈ test3
5∈test3 = here

6∈test3 : 6 ∈ test3
6∈test3 = right here

data RightHeavyAvl (A : Set) (lower upper : ℕ∞) : ℕ → Set where --the last element is the height of the tree
  rightheavynode : {l r : ℕ} → (n : ℕ)
            → Avl A lower [ n ] l
            → Avl A [ n ] upper r
            --→ 1 ≤ r --l < r
            → r ≡ 1 + l --r - l ≤ 1
            → RightHeavyAvl A lower upper (r + 1)

data LeftHeavyAvl (A : Set) (lower upper : ℕ∞) : ℕ → Set where
  leftheavynode : {l r : ℕ} → (n : ℕ)
            → Avl A lower [ n ] l
            → Avl A [ n ] upper r
            → l ≡ 1 + r
            → LeftHeavyAvl A lower upper (l + 1)


data AlmostAvlRight (A : Set) (lower upper : ℕ∞) : ℕ → Set where --the last element is the height of the tree
  almostrightnode : {l r : ℕ} → (n : ℕ)
            → Avl A lower [ n ] l
            → RightHeavyAvl A [ n ] upper r
            --→ 2 ≤ r --l < r
            → r ≡ 2 + l --r - l ≡ 2
            → AlmostAvlRight A lower upper (r + 1)


data AlmostAvlLeft (A : Set) (lower upper : ℕ∞) : ℕ → Set where --the last element is the height of the tree
  almostleftnode : {l r : ℕ} → (n : ℕ)
            → Avl A lower [ n ] l
            → Avl A [ n ] upper r
            → l ≡ 2 + r
            → AlmostAvlLeft A lower upper (l + 1)


proof1 : ∀ n → n + 1 -ᴺ 1 ≡ n
proof1 n = (begin 
            n + 1 -ᴺ 1 ≡⟨ +-∸-assoc n (s≤s z≤n) ⟩
            n + (1 -ᴺ 1) ≡⟨ refl ⟩
            n + 0 ≡⟨ +-comm n 0 ⟩
            0 + n ≡⟨ refl ⟩
            n
            ∎)

proof1rev : (n : ℕ) → 1 ≤ n → n -ᴺ 1 + 1 ≡ n
proof1rev n p = (begin 
            n -ᴺ 1 + 1 ≡⟨ m∸n+n≡m p ⟩
            n
            ∎)

proof2 : (n : ℕ) → 1 ≤ n → n + 1 -ᴺ 1 ≡ n -ᴺ 1 + 1
proof2 n p = (begin
            n + 1 -ᴺ 1 ≡⟨ proof1 n ⟩
            n ≡⟨ sym (proof1rev n p) ⟩
            n -ᴺ 1 + 1
            ∎)

proof3 : ∀ {m n} → m ≡ 1 + n → n ≤ m
proof3 {.(1 + n)} {n} refl = n≤1+n n

proof4,0 : ∀ {m n} → m + 1 ≡ suc n → m ≡ n
proof4,0 {m} {n} p = {!   !}

proof4 : ∀ {m n o} → m ≤ n → m ⊔ n + 1 ≡ suc (suc o) → n ≡ suc o
proof4 {m} {n} {o} p q = (begin
                          n ≡⟨ sym (m≤n⇒m⊔n≡n p) ⟩
                          m ⊔ n ≡⟨ {!   !} ⟩ --cong {!  !} {!   !} ⟩
                          suc o
                          ∎)


leftRotation : {lower upper : ℕ∞} {h : ℕ} → AlmostAvlRight ℕ lower upper h → Avl ℕ lower upper (h -ᴺ 1)
leftRotation (almostrightnode {l = l₁} {r = r₁} n l (rightheavynode {l = l₂} {r = r₂} rn rl rr rx) x) 
    rewrite proof1 (r₂ + 1) rewrite sym(m≤n⇒m⊔n≡n (proof3 rx)) = node rn (node n {! l  !} rl {!   !}) rr {!   !} --node {l = l₂} {r = r₂} rn {!   !} {! rr  !} {!   !} 
--subst {!   !} {!   !} {!   !} 
{-node rn (node n l rl (≤-trans (≤-reflexive 
    (begin
      l₂ - l₁ ≡⟨ cong (λ x → x - l₁) rx ⟩
      (r₂ - 1) - l₁ ≡⟨ cong (λ x → (r₂ - 1) - x) x ⟩
      (r₂ - 1) - (r₂ - 1) ≡⟨ abszero (r₂ - 1) ⟩
      0
    ∎)) z≤n)) {!   !} {!   !} -}


rightRotation : {lower upper : ℕ∞} {h : ℕ} → Avl ℕ lower upper h → Avl ℕ lower upper h
rightRotation t = {!   !}

{-
insert : {lower upper : ℕ∞} {h h2 : ℕ} → (n : ℕ) → Avl ℕ lower upper h → Avl ℕ lower upper h2
insert n t = {!   !}
-}





   