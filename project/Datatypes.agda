{-# OPTIONS --allow-unsolved-metas #-}
module Datatypes where

open import Agda.Builtin.Nat using () renaming (_-_ to _-ᴺ_)
open import Data.Nat renaming (∣_-_∣ to _-_)
open import Data.Nat.Properties
open import Data.List using (List; []; _∷_; length)
open import Data.Bool.Base using (T; if_then_else_)
open import Agda.Builtin.Bool public
open import Data.Maybe
open import Data.Sum.Base
open import Relation.Nullary
open import Data.Bool.Properties using (T?)
open import Data.Empty
open import Relation.Binary.Definitions
open import Agda.Builtin.Sigma
open import Data.Product

import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; sym; trans; cong; subst; resp)
open Eq.≡-Reasoning using (begin_; _≡⟨⟩_; step-≡; _∎)
open import Axiom.Extensionality.Propositional using (Extensionality)

data ℕ∞ : Set where
  -∞  :     ℕ∞
  [_] : ℕ → ℕ∞
  +∞  :     ℕ∞

data _<∞_ : ℕ∞ → ℕ∞ → Set where
  -∞<n  : {n   : ℕ∞}  →          -∞   <∞   n
  []<[] : {n m : ℕ}   → n < m → [ n ] <∞ [ m ]
  n<+∞  : {n   : ℕ∞}  →           n   <∞  +∞


data Avl (A : Set) (lower upper : ℕ∞) : ℕ → Set where       --the last element is the height of the tree
  empty : (p : lower <∞ upper) → Avl A lower upper zero
  node : {l r : ℕ} → (n : ℕ)
            → Avl A lower [ n ] l
            → Avl A [ n ] upper r
            → (r - l) ≤ 1
            → Avl A lower upper ((l ⊔ r) + 1)

data _∈_ (n : ℕ) : {lower upper : ℕ∞} {h : ℕ} → Avl ℕ lower upper h → Set where
  here : ∀ {ll rr hl hr} → {l : Avl ℕ ll [ n ] hl} {r : Avl ℕ [ n ] rr hr} {p : (hr - hl) ≤ 1} → n ∈ node n l r p
  left : ∀ {ll rr hl hr x} → {l : Avl ℕ ll [ x ] hl} {r : Avl ℕ [ x ] rr hr} {p : (hr - hl) ≤ 1} → n ∈ l → n ∈ node x l r p
  right : ∀ {ll rr hl hr x} → {l : Avl ℕ ll [ x ] hl} {r : Avl ℕ [ x ] rr hr} {p : (hr - hl) ≤ 1} → n ∈ r → n ∈ node x l r p

data RightHeavyAvl (A : Set) (lower upper : ℕ∞) : ℕ → Set where --the last element is the height of the tree
  rightheavynode : {l r : ℕ} → (n : ℕ)
            → Avl A lower [ n ] l
            → Avl A [ n ] upper r
            → r ≡ 1 + l
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
            → r ≡ 2 + l
            → AlmostAvlRight A lower upper (r + 1)


data AlmostAvlLeft (A : Set) (lower upper : ℕ∞) : ℕ → Set where --the last element is the height of the tree
  almostleftnode : {l r : ℕ} → (n : ℕ)
            → LeftHeavyAvl A lower [ n ] l
            → Avl A [ n ] upper r
            → l ≡ 2 + r
            → AlmostAvlLeft A lower upper (l + 1)

data AlmostAvlLeftDouble (A : Set) (lower upper : ℕ∞) : ℕ → Set where --the last element is the height of the tree
  almostleftnodedouble : {l r : ℕ} → (n : ℕ)
            → RightHeavyAvl A lower [ n ] l
            → Avl A [ n ] upper r
            → l ≡ 2 + r
            → AlmostAvlLeftDouble A lower upper (l + 1)

data AlmostAvlRightDouble (A : Set) (lower upper : ℕ∞) : ℕ → Set where --the last element is the height of the tree
  almostrightnodedouble : {l r : ℕ} → (n : ℕ)
            → Avl A lower [ n ] l
            → LeftHeavyAvl A [ n ] upper r
            → r ≡ 2 + l
            → AlmostAvlRightDouble A lower upper (r + 1)

data InsertTree (lower upper : ℕ∞) : ℕ → Set where
  avl : {l r : ℕ} → (n : ℕ)
        → Avl ℕ lower [ n ] l
        → Avl ℕ [ n ] upper r
        → r - l ≤ 1
        → InsertTree lower upper (suc (l ⊔ r))
  llRot : {h : ℕ} → (n ln : ℕ)
          → Avl ℕ lower [ ln ] (h + 1)
          → Avl ℕ [ ln ] [ n ] h
          → Avl ℕ [ n ] upper h
          → InsertTree lower upper (h + 1 + 1)
  rrRot : {h : ℕ} → (n rn : ℕ)
          → (t1 : Avl ℕ lower [ n ] h)
          → (t2 : Avl ℕ [ n ] [ rn ] h)
          → (t3 : Avl ℕ [ rn ] upper (h + 1))
          → InsertTree lower upper (h + 1 + 1)
  lrRotL : {h : ℕ} → (n ln lrn : ℕ)
            → Avl ℕ lower [ ln ] (h + 1)
            → Avl ℕ [ ln ] [ lrn ] (h + 1)
            → Avl ℕ [ lrn ] [ n ] h
            → Avl ℕ [ n ] upper (h + 1)
            → InsertTree lower upper (h + 1 + 1 + 1)
  lrRotR : {h : ℕ} → (n ln lrn : ℕ)
            → Avl ℕ lower [ ln ] (h + 1)
            → Avl ℕ [ ln ] [ lrn ] h
            → Avl ℕ [ lrn ] [ n ] (h + 1)
            → Avl ℕ [ n ] upper (h + 1)
            → InsertTree lower upper (h + 1 + 1 + 1)
  rlRotL : {h : ℕ} → (n rn rln : ℕ)
            → Avl ℕ lower [ n ] (h + 1)
            → Avl ℕ [ n ] [ rln ] (h + 1)
            → Avl ℕ [ rln ] [ rn ] h
            → Avl ℕ [ rn ] upper (h + 1)
            → InsertTree lower upper (h + 1 + 1 + 1)
  rlRotR : {h : ℕ} → (n rn rln : ℕ)
            → Avl ℕ lower [ n ] (h + 1)
            → Avl ℕ [ n ] [ rln ] h
            → Avl ℕ [ rln ] [ rn ] (h + 1)
            → Avl ℕ [ rn ] upper (h + 1)
            → InsertTree lower upper (h + 1 + 1 + 1)
  rlRotInit : {h : ℕ} → (n rn rln : ℕ)
            → Avl ℕ lower [ n ] h
            → Avl ℕ [ n ] [ rln ] h
            → Avl ℕ [ rln ] [ rn ] h
            → Avl ℕ [ rn ] upper h
            → InsertTree lower upper (h + 1 + 1)
  lrRotInit : {h : ℕ} → (n ln lrn : ℕ)
            → Avl ℕ lower [ ln ] h
            → Avl ℕ [ ln ] [ lrn ] h
            → Avl ℕ [ lrn ] [ n ] h
            → Avl ℕ [ n ] upper h
            → InsertTree lower upper (h + 1 + 1)

_⊓∞_ : (m n : ℕ∞) → ℕ∞
-∞ ⊓∞ _ = -∞
[ x ] ⊓∞ -∞ = -∞
[ x ] ⊓∞ [ x1 ] = [ (x ⊓ x1) ]
[ x ] ⊓∞ +∞ = [ x ]
+∞ ⊓∞ n = n

_⊔∞_ : (m n : ℕ∞) → ℕ∞
-∞ ⊔∞ n = n
[ x ] ⊔∞ -∞ = [ x ]
[ x ] ⊔∞ [ x1 ] = [ (x ⊔ x1) ]
[ x ] ⊔∞ +∞ = +∞
+∞ ⊔∞ n = +∞


