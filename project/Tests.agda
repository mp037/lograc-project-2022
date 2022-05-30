{-# OPTIONS --allow-unsolved-metas #-}
module Tests where

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
open import Datatypes

import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; sym; trans; cong; subst; resp)
open Eq.≡-Reasoning using (begin_; _≡⟨⟩_; step-≡; _∎)
open import Axiom.Extensionality.Propositional using (Extensionality)

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

3∈test3 : 3 ∈ test3
3∈test3 = left here

5∈test3 : 5 ∈ test3
5∈test3 = here

6∈test3 : 6 ∈ test3
6∈test3 = right here

almostAvlLeftTest : AlmostAvlLeft ℕ -∞ +∞ 3
almostAvlLeftTest = almostleftnode 3 (leftheavynode 2 (node 1 (empty -∞<n) (empty ([]<[] (s≤s (s≤s z≤n)))) z≤n) (empty ([]<[] (s≤s (s≤s (s≤s z≤n))))) refl) (empty n<+∞) refl 

testTree1 : Avl ℕ -∞ [ 4 ] 2
testTree1 = node 2 (node 1 (empty -∞<n) (empty ([]<[] (s≤s (s≤s z≤n)))) z≤n) (empty ([]<[] (s≤s (s≤s (s≤s z≤n))))) (s≤s z≤n)

testTree2 : Avl ℕ [ 4 ] +∞ 1
testTree2 = node 5 (empty ([]<[] (s≤s (s≤s (s≤s (s≤s (s≤s z≤n))))))) (empty n<+∞) z≤n

testInsertTree : InsertTree -∞ +∞ 3
testInsertTree = avl 4 testTree1 testTree2 (s≤s z≤n)
