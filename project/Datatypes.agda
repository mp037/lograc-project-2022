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
open import Relation.Binary.Core

import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; sym; trans; cong; subst; resp; _≢_)
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

data _≤∞_ : ℕ∞ → ℕ∞ → Set where
  -∞≤n : {n : ℕ∞} → -∞ ≤∞ n
  []≤[] : {n m : ℕ} → n ≤ m → [ n ] ≤∞ [ m ]
  n≤+∞ : {n : ℕ∞} → n ≤∞ +∞


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
        → InsertTree lower upper ((l ⊔ r) + 1)
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

m≤∞n⇒m⊔∞n≡n : ∀ {m n} → m ≤∞ n → m ⊔∞ n ≡ n
m≤∞n⇒m⊔∞n≡n { -∞} {n} p = refl
m≤∞n⇒m⊔∞n≡n {[ x ]} {[ x₁ ]} ([]≤[] x₂) rewrite m≤n⇒m⊔n≡n x₂ = refl
m≤∞n⇒m⊔∞n≡n {[ x ]} {+∞} p = refl
m≤∞n⇒m⊔∞n≡n {+∞} {+∞} p = refl

<∞⇒≤∞ : _<∞_ ⇒ _≤∞_
<∞⇒≤∞ -∞<n = -∞≤n
<∞⇒≤∞ ([]<[] x) = []≤[] (<⇒≤ x)
<∞⇒≤∞ n<+∞ = n≤+∞

{-
data HeightIncTree {h : ℕ} {lower upper : ℕ∞} : Avl ℕ lower upper h → Set where
  tree-is-node : {l r n : ℕ}
              → l ≢ r 
              → (left : Avl ℕ lower [ n ] l) 
              → (right : Avl ℕ [ n ] upper r) 
              → (p : (r - l) ≤ 1) 
              → (p2 : l ⊔ r + 1 ≡ h)
              → HeightIncTree (subst (Avl ℕ lower upper) p2 (node n left right p))

data HeightIncTree2 {h : ℕ} {lower upper : ℕ∞} : InsertTree lower upper h → Set where
  tree-is-node2 : {l r n : ℕ}
                → l ≢ r 
                → (left : Avl ℕ lower [ n ] l) 
                → (right : Avl ℕ [ n ] upper r) 
                → (p : (r - l) ≤ 1) 
                → (p2 : l ⊔ r + 1 ≡ h)
                → HeightIncTree2 (subst (InsertTree lower upper) p2 (avl n left right p))

data HeightIncTreeInit {h : ℕ} {lower upper : ℕ∞} : Avl ℕ lower upper h → Set where
  basic-tree : {l r n : ℕ}
              → l ≡ 0
              → r ≡ 0
              → (left : Avl ℕ lower [ n ] l) 
              → (right : Avl ℕ [ n ] upper r) 
              → (p : (r - l) ≤ 1) 
              → (p2 : l ⊔ r + 1 ≡ h)
              → HeightIncTreeInit (subst (Avl ℕ lower upper) p2 (node n left right p))
-}


data HeightIncTreeInit : {h : ℕ} {lower upper : ℕ∞} → Avl ℕ lower upper h → Set where
  basic-tree : {n : ℕ} {h : ℕ} {lower upper : ℕ∞}
              → (left : Avl ℕ lower [ n ] 0) 
              → (right : Avl ℕ [ n ] upper 0) 
              → HeightIncTreeInit (node n left right z≤n) 

data HeightIncTreeInit2 : {h : ℕ} {lower upper : ℕ∞} → Avl ℕ lower upper h → Set where
  left-is-init : {l n : ℕ} {h : ℕ} {lower upper : ℕ∞}
                → (left : Avl ℕ lower [ n ] l)
                → (right : Avl ℕ [ n ] upper 0)
                → (leftInit : HeightIncTreeInit left)
                → (p : (0 - l) ≤ 1) 
                → (p2 : l ⊔ 0 + 1 ≡ h)
                → HeightIncTreeInit2 (node n left right p)
  right-is-init : {r n : ℕ} {h : ℕ} {lower upper : ℕ∞}
                → (left : Avl ℕ lower [ n ] 0)
                → (right : Avl ℕ [ n ] upper r)
                → (rightInit : HeightIncTreeInit right)
                → (p : (r - 0) ≤ 1) 
                → (p2 : 0 ⊔ r + 1 ≡ h)
                → HeightIncTreeInit2 (node n left right p)


data HeightIncTree3 : {h h' : ℕ} {lower upper lower' upper' : ℕ∞} → Avl ℕ lower upper h → Avl ℕ lower' upper' h' → Set where
  left-subtree : {r l' r' n n' : ℕ} {h h' : ℕ} {lower upper : ℕ∞}
                → l' ≢ r'
                → (left' : Avl ℕ lower [ n' ] l') 
                → (right' : Avl ℕ [ n' ] [ n ] r')
                → (p' : (r' - l') ≤ 1)
                → (p2' : l' ⊔ r' + 1 ≡ h')
                → (right : Avl ℕ [ n ] upper r)
                → (p : r - (l' ⊔ r' + 1) ≤ 1)
                → (p2 : l' ⊔ r' + 1 ⊔ r + 1 ≡ h)
                → HeightIncTree3 (node n (node n' left' right' p') right p) (node n' left' right' p')
  right-subtree : {l l' r' n n' : ℕ} {h h' : ℕ} {lower upper : ℕ∞}
                  → l' ≢ r'
                  → (left' : Avl ℕ [ n ] [ n' ] l')
                  → (right' : Avl ℕ [ n' ] upper r')
                  → (p' : (r' - l') ≤ 1)
                  → (p2' : l' ⊔ r' + 1 ≡ h')
                  → (left : Avl ℕ lower [ n ] l)
                  → (p : (l' ⊔ r' + 1) - l ≤ 1)
                  → (p2 : l ⊔ (l' ⊔ r' + 1) + 1 ≡ h)
                  → HeightIncTree3 (node n left (node n' left' right' p') p) (node n' left' right' p')

{-data HeightIncTree3 {h h' : ℕ} {lower upper lower' upper' : ℕ∞} : Avl ℕ lower upper h → Avl ℕ lower' upper' h' → Set where
  left-subtree : {l r l' r' n n' : ℕ} --remove l?
                → l' ≢ r'
                → (left' : Avl ℕ lower' [ n' ] l') 
                → (right' : Avl ℕ [ n' ] upper' r')
                → (p' : (r' - l') ≤ 1)
                → (p2' : l' ⊔ r' + 1 ≡ h')
                → (right : Avl ℕ [ n ] upper r)
                → (p : r - (l' ⊔ r' + 1) ≤ 1)
                → (p2 : l' ⊔ r' + 1 ⊔ r + 1 ≡ h)
                → (p3 : upper' ≡ [ n ])
                → (p4 : lower' ≡ lower)
                → HeightIncTree3 (subst (λ x → Avl ℕ x upper h) p4 
                                  (subst (Avl ℕ lower' upper) p2 
                                    (node n (node n' left' (subst (λ x → Avl ℕ [ n' ] x r') p3 right') p') right p))) 
                                (subst (Avl ℕ lower' upper') p2' (node n' left' right' p'))
  right-subtree : {l r l' r' n n' : ℕ} --remove r?
                  → l' ≢ r'
                  → (left' : Avl ℕ lower' [ n' ] l')
                  → (right' : Avl ℕ [ n' ] upper' r')
                  → (p' : (r' - l') ≤ 1)
                  → (p2' : l' ⊔ r' + 1 ≡ h')
                  → (left : Avl ℕ lower [ n ] l)
                  → (p : (l' ⊔ r' + 1) - l ≤ 1)
                  → (p2 : l ⊔ (l' ⊔ r' + 1) + 1 ≡ h)
                  → (p3 : lower' ≡ [ n ])
                  → (p4 : upper' ≡ upper)
                  → HeightIncTree3 (subst (λ x → Avl ℕ lower x h) p4 
                                    (subst (Avl ℕ lower upper') p2 
                                      (node n left (node n' (subst (λ x → Avl ℕ x [ n' ] l') p3 left') right' p') p))) 
                                  (subst (Avl ℕ lower' upper') p2' (node n' left' right' p'))-}


  