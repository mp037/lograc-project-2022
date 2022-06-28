{-# OPTIONS --allow-unsolved-metas #-}
module Avl where

open import Agda.Builtin.Nat using () renaming (_-_ to _-ᴺ_)
open import Data.Nat renaming (∣_-_∣ to _-_)
open import Data.Nat.Properties
open import Data.List using (List; []; _∷_; length)
open import Data.Bool.Base using (T; if_then_else_)
open import Agda.Builtin.Bool public
open import Data.Maybe
open import Data.Sum.Base
open import Relation.Nullary
open import Relation.Nullary.Negation
open import Data.Bool.Properties using (T?)
open import Data.Empty
open import Relation.Binary.Definitions
open import Agda.Builtin.Sigma
open import Data.Product
open import Function.Base
open import Datatypes
open import Proofs

import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; sym; trans; cong; subst; resp)
open Eq.≡-Reasoning using (begin_; _≡⟨⟩_; step-≡; _∎)
open import Axiom.Extensionality.Propositional using (Extensionality)

postulate
  fun-ext : ∀ {a b} → Extensionality a b

depth : {lower upper : ℕ∞} {h : ℕ} → Avl ℕ lower upper h → ℕ
depth {lower} {upper} {h} t = h


search : (x : ℕ) {lower upper : ℕ∞} {h : ℕ} → (t : Avl ℕ lower upper h) → (x ∈ t) ⊎ (¬ (x ∈ t))
search x (empty p) = inj₂ (λ ())
search x (node n l r p) with x <? n | x >? n
... | no ¬p | no ¬p₁ rewrite sym (x</n,x>/n⇒x≡n ¬p ¬p₁) = inj₁ here
... | no ¬p | yes p₁ = x∈r⇒x∈t p₁ (search x r)
... | yes p₁ | rez2 = x∈l⇒x∈t p₁ (search x l)


leftRotation : {lower upper : ℕ∞} {h : ℕ} → AlmostAvlRight ℕ lower upper h → Avl ℕ lower upper (h -ᴺ 1)
leftRotation {lower} {upper} (almostrightnode {l = l₁} {r = r₁} n l (rightheavynode {l = l₂} {r = r₂} rn rl rr rx) x) rewrite proof1 (r₂ + 1) | sym (proof6 x rx)
    = node rn (node n l rl (proof8,1 x rx)) (subst (Avl ℕ [ rn ] upper) (proof6 x rx) rr) (proof10,2 x rx) 

rightRotation1 : {lower upper : ℕ∞} {h : ℕ}
                → (n rn : ℕ)
                → (t1 : Avl ℕ lower [ n ] h)
                → (t2 : Avl ℕ [ n ] [ rn ] h)
                → (t3 : Avl ℕ [ rn ] upper (h + 1))
                → Avl ℕ lower upper (h + 1 + 1)
rightRotation1 {lower} {upper} {h} n rn t1 t2 t3 = subst (Avl ℕ lower upper) (proof17 {h}) (node rn (node n t1 t2 (proof15 {h})) t3 (proof16,1 {h}))

leftRotation1 : {lower upper : ℕ∞} {h : ℕ}
                → (n ln : ℕ)
                → (t1 : Avl ℕ lower [ ln ] (h + 1))
                → (t2 : Avl ℕ [ ln ] [ n ] h)
                → (t3 : Avl ℕ [ n ] upper h)
                → Avl ℕ lower upper (h + 1 + 1)
leftRotation1 {lower} {upper} {h} n ln t1 t2 t3 = subst (Avl ℕ lower upper) (proof17,1 {h}) (node ln t1 (node n t2 t3 (proof15 {h})) (proof16,2 {h}))

leftRightRotationL : {lower upper : ℕ∞} {h : ℕ}
                    → (n ln lrn : ℕ)
                    → (t1 : Avl ℕ lower [ ln ] (h + 1))
                    → (t2 : Avl ℕ [ ln ] [ lrn ] (h + 1))
                    → (t3 : Avl ℕ [ lrn ] [ n ] h)
                    → (t4 : Avl ℕ [ n ] upper (h + 1))
                    → Avl ℕ lower upper (h + 1 + 1 + 1)
leftRightRotationL {lower} {upper} {h} n ln lrn t1 t2 t3 t4 = subst (Avl ℕ lower upper) (proof18 {h}) (node lrn (node ln t1 t2 (proof15 {h + 1})) (node n t3 t4 (proof16,01 {h})) (proof19 {h}))

leftRightRotationR : {lower upper : ℕ∞} {h : ℕ}
                    → (n ln lrn : ℕ)
                    → (t1 : Avl ℕ lower [ ln ] (h + 1))
                    → (t2 : Avl ℕ [ ln ] [ lrn ] h)
                    → (t3 : Avl ℕ [ lrn ] [ n ] (h + 1))
                    → (t4 : Avl ℕ [ n ] upper (h + 1))
                    → Avl ℕ lower upper (h + 1 + 1 + 1)
leftRightRotationR {lower} {upper} {h} n ln lrn t1 t2 t3 t4 = subst (Avl ℕ lower upper) (proof18,1 {h}) (node lrn (node ln t1 t2 (proof16,02 {h})) (node n t3 t4 (proof15 {h + 1})) (proof19,1 {h}))

rightLeftRotationL : {lower upper : ℕ∞} {h : ℕ}
                    → (n rn rln : ℕ)
                    → (t1 : Avl ℕ lower [ n ] (h + 1))
                    → (t2 : Avl ℕ [ n ] [ rln ] (h + 1))
                    → (t3 : Avl ℕ [ rln ] [ rn ] h)
                    → (t4 : Avl ℕ [ rn ] upper (h + 1))
                    → Avl ℕ lower upper (h + 1 + 1 + 1)
rightLeftRotationL {lower} {upper} {h} n rn rln t1 t2 t3 t4 = subst (Avl ℕ lower upper) (proof18 {h}) (node rln (node n t1 t2 (proof15 {h + 1})) (node rn t3 t4 (proof16,01 {h})) (proof19 {h}))

rightLeftRotationR : {lower upper : ℕ∞} {h : ℕ}
                    → (n rn rln : ℕ)
                    → (t1 : Avl ℕ lower [ n ] (h + 1))
                    → (t2 : Avl ℕ [ n ] [ rln ] h)
                    → (t3 : Avl ℕ [ rln ] [ rn ] (h + 1))
                    → (t4 : Avl ℕ [ rn ] upper (h + 1))
                    → Avl ℕ lower upper (h + 1 + 1 + 1)
rightLeftRotationR {lower} {upper} {h} n rn rln t1 t2 t3 t4 = subst (Avl ℕ lower upper) (proof18,1 {h}) (node rln (node n t1 t2 (proof16,02 {h})) (node rn t3 t4 (proof15 {h + 1})) (proof19,1 {h}))

proof31 : ∀ {n} → n - n ≤ 1
proof31 {n} rewrite ∣n-n∣≡0 n = z≤n

rightLeftRotationInit : {lower upper : ℕ∞} {h : ℕ}
                    → (n rn rln : ℕ)
                    → (t1 : Avl ℕ lower [ n ] h)
                    → (t2 : Avl ℕ [ n ] [ rln ] h)
                    → (t3 : Avl ℕ [ rln ] [ rn ] h)
                    → (t4 : Avl ℕ [ rn ] upper h)
                    → Avl ℕ lower upper (h + 1 + 1)
rightLeftRotationInit {lower} {upper} {h} n rn rln t1 t2 t3 t4 = subst (Avl ℕ lower upper) (subst (λ x → x + 1 ≡ h + 1 + 1) (sym (⊔-idem (h ⊔ h + 1))) (subst (λ x → x + 1 + 1 ≡ h + 1 + 1) (sym (⊔-idem h)) refl)) (node rln (node n t1 t2 (proof31 {h})) (node rn t3 t4 (proof31 {h})) (proof31 {h ⊔ h + 1}))

rightRotation : {lower upper : ℕ∞} {h : ℕ} → AlmostAvlLeft ℕ lower upper h → Avl ℕ lower upper (h -ᴺ 1)
rightRotation {lower} (almostleftnode {l = l₁} {r = r₁} n (leftheavynode {l = l₂} {r = r₂} ln ll lr lx) r x) rewrite proof1 (l₂ + 1) | sym (proof6,2 x lx) 
    = node {l = l₂} {r = r₂ ⊔ r₁ + 1} ln (subst (Avl ℕ lower [ ln ]) (proof6,2 x lx) ll) (node n lr r (proof8 x lx)) (proof10 x lx)

{-
rightRotationDouble : {lower upper : ℕ∞} {h : ℕ} → AlmostAvlLeftDouble ℕ lower upper h → Avl ℕ lower upper (h -ᴺ 1)
rightRotationDouble  {lower} {upper} (almostleftnodedouble {l = l₁} {r = r₁} n 
    (rightheavynode {l = l₂} {r = r₂} ln ll (node {l = l₃} {r = r₃} lrn lrl lrr lrx) lx) r x) rewrite proof1 (r₂ + 1) | proof12 {l₃} {r₃}      --proof13 lx x
    = node lrn (node ln {!  ll !} lrl {!   !}) (node n {!   !} {!   !} {!   !}) {!   !}
-}

--(node n lrr r (proof11 x lrx))
--(subst {! Avl ℕ lower [ ln ]  !} (proof13 (cong suc lx) x) ll)
-- λ x → Avl ℕ lower [ ln ] (x + 1)
--(subst (Avl ℕ lower [ ln ]) (proof13 (cong suc lx) x) ll)
{-
proof23,0 : ∀ {m n o p} → n ≡ suc m → p - o ≤ 1 → m ⊔ n + 1 ≡ suc p → suc m ≤ n → m -ᴺ o ≡ 0
proof23,0 {m} {n} {o} {p} p1 p2 p3 p4 = ≤-antisym (≤-pred {!   !}) {!   !}

proof23 : ∀ {m n o p} → n ≡ suc m → p - o ≤ 1 → m ⊔ n + 1 ≡ suc p → suc m ≤ n → m ≡ o
proof23 {m} {n} {o} {p} p1 p2 p3 p4 = ≤-antisym (m∸n≡0⇒m≤n {!   !}) (m∸n≡0⇒m≤n {!   !})
-}

proof24 : ∀ {m n o} → m ≡ suc o → suc n ≤ o → n ⊔ m ≡ o + 1
proof24 {m} {n} {o} p1 p2 rewrite p1 | m≤n⇒m⊔n≡n (≤-step (<⇒≤ p2)) | +-comm o 1 = refl

proof25 : ∀ {m n o} → m ≤ o → n > o → m ≤ n
proof25 {m} {n} {o} p1 p2 = ≤-trans p1 (<⇒≤ p2)

proof26 : {m n : ℕ} → m - n ≤ (suc m) - n → m ≥ n
proof26 {zero} {zero} p = z≤n
proof26 {zero} {suc n} p = contradiction p 1+n≰n
proof26 {suc m} {zero} p = z≤n
proof26 {suc m} {suc n} p = s≤s (proof26 p)

testproof : ∀ {n} → ¬ n ≡ suc n
testproof {zero} = λ ()
testproof {suc n} = testproof ∘ suc-injective

--proof27,0 : ∀ {m n} → m ≡ n → ¬ m ≡ suc n
--proof27,0 {m} {n} p rewrite p = testproof

proof27,0 : ∀ {m n} → m ≡ suc n → ¬ m ≡ n
proof27,0 {m} {n} p rewrite p = 1+n≢n

{-
proof27 : ∀ {m n o p} → n ≡ suc m → p - o ≤ 1 → m ⊔ n + 1 ≡ suc p → suc m ≤ n → ((m ⊔ n + 1) - o ≤ 1 → ⊥) → m ≡ o
proof27 {m} {n} {o} {p} p1 p2 p3 p4 p5 = proof5 p1 p10
    where p6 : (p - o) ≤ ((m ⊔ n + 1) - o)
          p6 = proof25 p2 (≰⇒> p5)
          p7 : m ⊔ n ≥ o
          p7 = proof26 (subst (λ x → (x - o) ≤ (suc (m ⊔ n) - o)) (sym (proof4,0 p3)) (subst (λ x → (p - o) ≤ (x - o)) (+-comm (m ⊔ n) 1) p6))
          p8 : o ≤ n
          p8 = ≤-trans p7 (≤-reflexive (m≤n⇒m⊔n≡n (<⇒≤ p4)))
          p9 : n -ᴺ o ≤ 1
          p9 = subst (λ x → x ≤ 1) (m≤n⇒∣n-m∣≡n∸m p8) (subst (λ x → x - o ≤ 1) (subst (λ x → p ≡ x) ((m≤n⇒m⊔n≡n (<⇒≤ p4))) (sym (proof4,0 p3))) p2)
          p10 : n ≡ suc o
          p10 with n -ᴺ o <? 1 | n -ᴺ o >? 1
          ... | no ¬p | no ¬p₁ = subst (λ x → x ≡ suc o) (m∸n+n≡m p8) (cong (λ x → x + o) p11)
            where p11 = x</n,x>/n⇒x≡n ¬p ¬p₁
          ... | no ¬p | yes p₁ = contradiction p₁ (≤⇒≯ p9)
          ... | yes p₁ | rez2 = {! contradiction p12 (proof27,0 p10)  !} -- contradiction p12 (proof27,0 p10)    --p10 (proof27,0 p12)
            where p12 = subst (λ x → x ≡ o) (m∸n+n≡m p8) (cong (λ x → x + o) (n≤0⇒n≡0 (≤-pred p₁)))
-}


∣suc[n]-m∣≤1⇒∣suc[suc[n]]-m|>1⇒n≡m : ∀ {n m}
                                     → suc n - m ≤ 1
                                     → suc (suc n) - m > 1
                                     → n ≡ m
          
∣suc[n]-m∣≤1⇒∣suc[suc[n]]-m|>1⇒n≡m {zero} {zero} p q = refl
∣suc[n]-m∣≤1⇒∣suc[suc[n]]-m|>1⇒n≡m {zero} {suc .zero} z≤n (s≤s ())
∣suc[n]-m∣≤1⇒∣suc[suc[n]]-m|>1⇒n≡m {zero} {suc .1} (s≤s z≤n) ()
∣suc[n]-m∣≤1⇒∣suc[suc[n]]-m|>1⇒n≡m {suc n} {zero} (s≤s ()) q
∣suc[n]-m∣≤1⇒∣suc[suc[n]]-m|>1⇒n≡m {suc n} {suc m} p q = cong suc (∣suc[n]-m∣≤1⇒∣suc[suc[n]]-m|>1⇒n≡m p q)


∣n-m∣≤1⇒∣suc[n]-m|>1⇒n≡suc[m] : ∀ {n m} → n - m ≤ 1 → suc n - m > 1 → n ≡ suc m
∣n-m∣≤1⇒∣suc[n]-m|>1⇒n≡suc[m] {zero} {zero} p1 p2 = contradiction p2 (<⇒≱ (s≤s (s≤s z≤n)))
∣n-m∣≤1⇒∣suc[n]-m|>1⇒n≡suc[m] {zero} {suc (suc m)} p1 p2 = contradiction p1 (<⇒≱  (≤-step p2))
∣n-m∣≤1⇒∣suc[n]-m|>1⇒n≡suc[m] {suc n} {zero} p1 p2 rewrite n≤0⇒n≡0 (≤-pred p1) = proof20 (<⇒≱ p2) (<⇒≱ p2)
∣n-m∣≤1⇒∣suc[n]-m|>1⇒n≡suc[m] {suc n} {suc m} p1 p2 = cong suc (∣n-m∣≤1⇒∣suc[n]-m|>1⇒n≡suc[m] p1 p2)

proof27' : ∀ {m n o p} → n ≡ suc m → p - o ≤ 1 → 1 + (m ⊔ n) ≡ suc p → suc m ≤ n → ((1 + (m ⊔ n)) - o ≤ 1 → ⊥) → m ≡ o
proof27' {m = m} refl p2 refl p4 p5 rewrite ⊔-idem m | m≤n⇒m⊔n≡n (m≤n+m m 1) =
  ∣suc[n]-m∣≤1⇒∣suc[suc[n]]-m|>1⇒n≡m p2 (≰⇒> p5)

proof27,1 : ∀ {m n o} → n ≡ suc m → m ≡ o → n ≡ o + 1
proof27,1 {m} {n} {o} p1 p2 rewrite +-comm o 1 | sym p2 = p1

proof28 : ∀ {m n} → m + 1 ≡ suc n → ¬ (1 ≤ m) → n ≡ 0
proof28 {m} {n} p1 p2 rewrite sym (proof4,0 p1) = n<1⇒n≡0 (≰⇒> p2)

proof29 : ∀ {m n} → m ≡ 0 → m - n ≤ 1 → n ≤ 1
proof29 {m} {n} p1 p2 = subst (λ x → x - n ≤ 1) p1 p2

proof30 : ∀ {n} → 1 - n > 1 → n > 2
proof30 {zero} p = contradiction p (<⇒≱ (s≤s (s≤s z≤n)))
proof30 {suc (suc zero)} p = contradiction p (<⇒≱  (s≤s (s≤s z≤n)))
proof30 {suc (suc (suc n))} p = s≤s p


insert : {lower upper : ℕ∞} {h : ℕ} → (x : ℕ) → Avl ℕ lower upper h → (p1 : lower <∞ [ x ]) → (p2 : [ x ] <∞ upper) → Σ[ h' ∈ ℕ ] ((Avl ℕ ([ x ] ⊓∞ lower) ([ x ] ⊔∞ upper) h') × ((h' ≡ h) ⊎ (h' ≡ suc h)) × (0 < h'))

insert' : {lower upper : ℕ∞} {h : ℕ} → (x : ℕ) → Avl ℕ lower upper h → (p1 : lower <∞ [ x ]) → (p2 : [ x ] <∞ upper) → Σ[ h' ∈ ℕ ] ((InsertTree lower upper h') × ((h' ≡ h) ⊎ (h' ≡ suc h)))
insert' x (empty p) p1 p2 = 1 , (avl x (empty p1) (empty p2) z≤n) ,′ inj₂ refl
insert' x (node {l = l₁} {r = r₁} n l r p) p1 p2 with x <? n | x >? n --? n | x >? n
insert' x (node {l = l₁} {r = r₁} n l r p) p1 p2 | no ¬p | no ¬p₁ rewrite sym (x</n,x>/n⇒x≡n ¬p ¬p₁) = suc (l₁ ⊔ r₁) , (avl {l = l₁} {r = r₁} x l r p) ,′ inj₁ (+-comm 1 (l₁ ⊔ r₁))
insert' x (node {l = l₁} {r = r₁} n l r p) p1 p2 | no ¬p | yes p₁ with newT
    where newT = insert x r ([]<[] p₁) p2 -- inserting in the right subtree
insert' x (node {l = l₁} {r = r₁} n l r p) p1 p2 | no ¬p | yes p₁ | fst₁ , fst₂ , inj₁ x₁ , snd₁ rewrite m≥n⇒m⊓n≡n (<⇒≤ p₁) | []<∞n⇒[]⊔∞n≡n p2 | sym x₁ = suc (l₁ ⊔ fst₁) , (avl n l fst₂ p) ,′ inj₁ (+-comm 1 (l₁ ⊔ fst₁))
insert' x (node {l = l₁} {r = r₁} n l r p) p1 p2 | no ¬p | yes p₁ | fst₁ , fst₂ , inj₂ y , snd₁ with fst₁ - l₁ ≤? 1 --? 1
insert' x (node {l = l₁} {r = r₁} n l r p) p1 p2 | no ¬p | yes p₁ | .(d1 ⊔ d2 + 1) , node {l = d1} {r = d2} n₁ fst₂ fst₃ x₁ , inj₂ y , snd₁ | no ¬p₁ with d2 >? d1 | d2 <? d1 --check if rightLeaning
insert' x (node {l = l₁} {r = r₁} n l r p) p1 p2 | no ¬p | yes p₁ | .(zero ⊔ d2 + _) , node {l = .zero} {r = d2} n₁ (empty p₂) fst₃ x₁ , inj₂ y , snd₁ | no ¬p₁ | no ¬p₂ | rez2 = contradiction (proof30 (≰⇒> (subst (λ x → ((x + 1) - l₁) ≤ 1 → ⊥) (n<1⇒n≡0 (≰⇒> ¬p₂)) ¬p₁))) (<⇒≱  (s≤s (≤-step (proof29 (proof28 y ¬p₂) p))))
insert' x (node {l = l₁} {r = r₁} n l r p) p1 p2 | no ¬p | yes p₁ | .(ld1 ⊔ ld2 + 1 ⊔ d2 + _) , node {l = .(ld1 ⊔ ld2 + 1)} {r = d2} n₁ (node {l = ld1} {r = ld2} n₂ fst₂ fst₄ x₂) fst₃ x₁ , inj₂ y , snd₁ | no ¬p₁ | no ¬p₂ | no ¬p₃ = {!   !} -- d1=d2
insert' x (node {l = l₁} {r = r₁} n l r p) p1 p2 | no ¬p | yes p₁ | .(ld1 ⊔ ld2 + 1 ⊔ d2 + _) , node {l = .(ld1 ⊔ ld2 + 1)} {r = d2} n₁ (node {l = ld1} {r = ld2} n₂ fst₂ fst₄ x₂) fst₃ x₁ , inj₂ y , snd₁ | no ¬p₁ | no ¬p₂ | yes p₂ with ld2 >? ld1 | ld2 <? ld1
insert' x (node {l = l₁} {r = r₁} n l r p) p1 p2 | no ¬p | yes p₁ | .(ld1 ⊔ ld2 + _ ⊔ d2 + _) , node {.(ld1 ⊔ ld2 + _)} {r = d2} n₁ (node {l = ld1} {r = ld2} n₂ fst₂ fst₄ x₂) fst₃ x₁ , inj₂ y , snd₁ | no ¬p₁ | no ¬p₂ | yes p₂ | false because proof₁ | rez2 = {!   !}
insert' x (node {l = l₁} {r = r₁} n l r p) p1 p2 | no ¬p | yes p₁ | .(ld1 ⊔ ld2 + _ ⊔ d2 + _) , node {.(ld1 ⊔ ld2 + _)} {r = d2} n₁ (node {l = ld1} {r = ld2} n₂ fst₂ fst₄ x₂) fst₃ x₁ , inj₂ y , snd₁ | no ¬p₁ | no ¬p₂ | yes p₂ | yes p₃ | rez2
    = {! ? , (rlRotR n n₁ n₂ l fst₂ fst₄ fst₃) ,′ ?  !}
    where p3 : r₁ ≡ suc l₁
          p3 = ∣n-m∣≤1⇒∣suc[n]-m|>1⇒n≡suc[m] p (≰⇒> (subst (λ x → x - l₁ ≤ 1 → ⊥) y ¬p₁))
          p4 : ld1 ⊔ ld2 ≡ ld2
          p4 = m≤n⇒m⊔n≡n (<⇒≤ p₃)
          p5 : ld2 ≡ suc ld1
          p5 = proof22 x₂ p₃
          p6 : ld2 ≡ d2
          p6 = suc-injective (subst (λ x → x ≡ suc d2) (+-comm ld2 1) (proof22 (subst (λ x → x ≤ 1) (∣-∣-comm d2 (ld2 + 1)) (subst (λ x → d2 - (x + 1) ≤ 1) p4 x₁)) (subst (λ x → suc d2 ≤ x + 1) p4 p₂)))
          p7 : r₁ ≡ suc ld2
          p7 = suc-injective (sym (subst (λ x → x ≡ suc r₁) (sym (+-comm 1 (suc ld2))) (subst (λ x → x ≡ suc r₁) (sym (+-comm 1 (ld2 + 1))) (subst (λ x → x + 1 ≡ suc r₁) (m≥n⇒m⊔n≡m (subst (λ x → x ≥ d2) (+-comm 1 ld2) (subst (λ x → suc ld2 ≥ x) p6 (n≤1+n ld2)))) (subst (λ x → x + 1 ⊔ d2 + 1 ≡ suc r₁) p4 y)))))
          p8 : l₁ ≡ ld2
          p8 = suc-injective (subst (λ x → x ≡ suc ld2) p3 p7)
          p9 : l₁ ≡ ld1 + 1
          p9 rewrite +-comm ld1 1 | sym p5 = p8
--insert' x (node {l = l₁} {r = r₁} n l r p) p1 p2 | no ¬p | yes p₁ | .(ld1 ⊔ ld2 + _ ⊔ d2 + _) , node {l = .(ld1 ⊔ ld2 + 1)} {r = d2} n₁ (node {l = ld1} {r = ld2} n₂ fst₂ fst₄ x₂) fst₃ x₁ , inj₂ y , snd₁ | no ¬p₁ | no ¬p₂ rez = ?
-- with ld2 >? ld1 | ld2 <? ld1
--insert' x (node {l = l₁} {r = r₁} n l r p) p1 p2 | no ¬p | yes p₁ | .(ld1 ⊔ ld2 + 1 ⊔ d2 + 1) , node {.(ld1 ⊔ ld2 + 1)} {r = d2} n₁ (node {l = ld1} {r = ld2} n₂ fst₂ fst₄ x₂) fst₃ x₁ , inj₂ y , snd₁ | no ¬p₁ | no ¬p₂ | no ¬p₃ | no ¬p₄ = {!   !}
--insert' x (node {l = l₁} {r = r₁} n l r p) p1 p2 | no ¬p | yes p₁ | .(ld1 ⊔ ld2 + _ ⊔ d2 + _) , node {.(ld1 ⊔ ld2 + _)} {r = d2} n₁ (node {l = ld1} {r = ld2} n₂ fst₂ fst₄ x₂) fst₃ x₁ , inj₂ y , snd₁ | no ¬p₁ | no ¬p₂ | no ¬p₃ | yes p₂ = {!   !}
--insert' x (node {l = l₁} {r = r₁} n l r p) p1 p2 | no ¬p | yes p₁ | .(ld1 ⊔ ld2 + _ ⊔ d2 + _) , node {.(ld1 ⊔ ld2 + _)} {r = d2} n₁ (node {l = ld1} {r = ld2} n₂ fst₂ fst₄ x₂) fst₃ x₁ , inj₂ y , snd₁ | no ¬p₁ | no ¬p₂ | yes p₂ | rez2 
--    = {! ? , (rlRotR n n₁ n₂ l fst₂ fst₄ fst₃) ,′ ?  !}
insert' x (node {l = l₁} {r = r₁} n l r p) p1 p2 | no ¬p | yes p₁ | .(d1 ⊔ d2 + 1) , node {l = d1} {r = d2} n₁ fst₂ fst₃ x₁ , inj₂ y , snd₁ | no ¬p₁ | yes p₂ | rez rewrite m≥n⇒m⊓n≡n (<⇒≤ p₁) | []<∞n⇒[]⊔∞n≡n p2 | proof27' (proof22 x₁ p₂) p (subst (λ x → x ≡ suc r₁) (+-comm (d1 ⊔ d2) 1) y) p₂ (subst (λ x → (x - l₁ ≤ 1 → ⊥)) (+-comm (d1 ⊔ d2) 1) ¬p₁) | proof27,1 (proof22 x₁ p₂) (proof27' (proof22 x₁ p₂) p (subst (λ x → x ≡ suc r₁) (+-comm (d1 ⊔ d2) 1) y) p₂ (subst (λ x → (x - l₁ ≤ 1 → ⊥)) (+-comm (d1 ⊔ d2) 1) ¬p₁))
    = l₁ + 1 + 1 , (rrRot n n₁ l fst₂ fst₃) ,′ inj₁ (cong (λ x → x + 1) (subst (λ x → l₁ + 1 ≡ x) (sym (m≤n⇒m⊔n≡n (subst (λ x → l₁ ≤ x) (subst (λ x → x ≡ r₁) (m≤n⇒m⊔n≡n (<⇒≤ p₂)) (proof4,0 y)) (subst (λ x → l₁ ≤ x) (sym (proof27,1 (proof22 x₁ p₂) p3)) (subst (λ x → l₁ ≤ x) (+-comm 1 l₁) (n≤1+n l₁)))))) (subst (λ x → l₁ + 1 ≡ x) p4 (subst (λ x → l₁ + 1 ≡ x) (sym p5) (+-comm l₁ 1)))))
    where p3 : d1 ≡ l₁
          p3 = proof27' (proof22 x₁ p₂) p (subst (λ x → x ≡ suc r₁) (+-comm (d1 ⊔ d2) 1) y) p₂ (subst (λ x → (x - l₁ ≤ 1 → ⊥)) (+-comm (d1 ⊔ d2) 1) ¬p₁)
          p4 : d2 ≡ r₁
          p4 = subst (λ x → x ≡ r₁) (m≤n⇒m⊔n≡n (<⇒≤ p₂)) (proof4,0 y)
          p5 : d2 ≡ suc l₁
          p5 = subst (λ x → d2 ≡ suc x) p3 (proof22 x₁ p₂)
insert' x (node {l = l₁} {r = r₁} n l r p) p1 p2 | no ¬p | yes p₁ | fst₁ , fst₂ , inj₂ y , snd₁ | yes p₂ rewrite m≥n⇒m⊓n≡n (<⇒≤ p₁) | []<∞n⇒[]⊔∞n≡n p2 with l₁ <? r₁ | l₁ >? r₁ --? r₁ | l₁ >? r₁
insert' x (node {l = l₁} {r = r₁} n l r p) p1 p2 | no ¬p | yes p₁ | fst₁ , fst₂ , inj₂ y , snd₁ | yes p₂ | no ¬p₁ | no ¬p₂ rewrite sym (x</n,x>/n⇒x≡n ¬p₁ ¬p₂) | ⊔-idem l₁ = suc (l₁ ⊔ fst₁) , (avl n l fst₂ p₂) ,′ inj₂ (cong suc (subst (λ x → l₁ ⊔ x ≡ l₁ + 1) (sym y) (subst (λ x → x ≡ l₁ + 1) (sym (m≤n⇒m⊔n≡n (n≤1+n l₁))) (+-comm 1 l₁)))) 
insert' x (node {l = l₁} {r = r₁} n l r p) p1 p2 | no ¬p | yes p₁ | fst₁ , fst₂ , inj₂ y , snd₁ | yes p₂ | no ¬p₁ | yes p₃ rewrite m≥n⇒m⊔n≡m (<⇒≤ p₃) | +-comm l₁ 1 = suc (l₁ ⊔ fst₁) , (avl n l fst₂ p₂) ,′ inj₁ (cong suc (m≥n⇒m⊔n≡m (subst (λ x → l₁ ≥ x) (sym y) p₃)))
insert' x (node {l = l₁} {r = r₁} n l r p) p1 p2 | no ¬p | yes p₁ | fst₁ , fst₂ , inj₂ y , snd₁ | yes p₂ | yes p₃ | rez2 rewrite m≤n⇒m⊔n≡n (<⇒≤ p₃) = suc (l₁ ⊔ fst₁) , (avl n l fst₂ p₂) ,′ inj₂ (cong suc (proof24 y p₃))
insert' x (node {l = l₁} {r = r₁} n l r p) p1 p2 | yes p₁ | rez2 with newT --inserting in the left subtree
    where newT = insert x l p1 ([]<[] p₁)
insert' x (node {l = l₁} {r = r₁} n l r p) p1 p2 | yes p₁ | rez2 | fst₁ , fst₂ , inj₁ x₁ , snd₁ rewrite m≤n⇒m⊔n≡n (<⇒≤ p₁) | sym x₁ | n<∞[]⇒[]⊓∞n≡n p1 = suc (fst₁ ⊔ r₁) , (avl n fst₂ r p) ,′ inj₁ (+-comm 1 (fst₁ ⊔ r₁))
insert' x (node {l = l₁} {r = r₁} n l r p) p1 p2 | yes p₁ | rez2 | fst₁ , fst₂ , inj₂ y , snd₁ with r₁ - fst₁ ≤? 1 
insert' x (node {l = l₁} {r = r₁} n l r p) p1 p2 | yes p₁ | rez2 | .(d1 ⊔ d2 + 1) , node {l = d1} {r = d2} n₁ fst₂ fst₃ x₁ , inj₂ y , snd₁ | no ¬p with d1 >? d2 --check if leftLeaning 
insert' x (node {l = l₁} {r = r₁} n l r p) p1 p2 | yes p₁ | rez2 | .(d1 ⊔ d2 + _) , node {l = d1} {r = d2} n₁ fst₂ fst₃ x₁ , inj₂ y , snd₁ | no ¬p | false because proof₁ = {!   !}
insert' {lower} {upper} x (node {l = l₁} {r = r₁} n l r p) p1 p2 | yes p₁ | rez2 | .(d1 ⊔ d2 + _) , node {l = d1} {r = d2} n₁ fst₂ fst₃ x₁ , inj₂ y , snd₁ | no ¬p | yes p₂ rewrite m≤n⇒m⊔n≡n (<⇒≤ p₁) | proof22 (subst (λ x → x ≤ 1) (∣-∣-comm d2 d1) x₁) p₂ | +-comm 1 d2 | n<∞[]⇒[]⊓∞n≡n p1
    = d2 + 1 + 1 , (llRot n n₁ fst₂ fst₃ (subst (Avl ℕ [ n ] upper) (sym p3) r)) ,′ inj₁ (cong (λ x → x + 1) (subst (λ x → x ≡ l₁ ⊔ r₁) (+-comm 1 d2) (subst (λ x → x ≡ l₁ ⊔ r₁) (sym p5) (sym (m≥n⇒m⊔n≡m (subst (λ x → l₁ ≥ x) p3 (subst (λ x → x ≥ d2) p5 (n≤1+n d2))))))))
    where p4 : d1 ≡ suc d2
          p4 = proof22 (subst (λ x → x ≤ 1) (∣-∣-comm d2 d1) x₁) (subst (λ x → x ≤ d1) (+-comm d2 1) p₂) 
          p3 : d2 ≡ r₁
          p3 = proof27' p4 (subst (λ x → x ≤ 1) (∣-∣-comm r₁ l₁) p) (subst (λ x → x ≡ suc l₁) (+-comm (d2 ⊔ d1) 1) (subst (λ x → d2 ⊔ x + 1 ≡ suc l₁) (sym p4) (subst (λ x → d2 ⊔ x + 1 ≡ suc l₁) (+-comm d2 1) (subst (λ x → x + 1 ≡ suc l₁) (⊔-comm (d2 + 1) d2) y)))) (subst (λ x → x ≤ d1) (+-comm d2 1) p₂) (subst (λ x → (x ≤ 1 → ⊥)) (∣-∣-comm r₁ (suc (d2 ⊔ d1))) (subst (λ x → (r₁ - x ≤ 1 → ⊥)) (+-comm (d2 ⊔ d1) 1) (subst (λ x → (r₁ - (x + 1) ≤ 1 → ⊥)) (⊔-comm d1 d2) (subst (λ x → (r₁ - (x ⊔ d2 + 1) ≤ 1 → ⊥)) (sym p4) (subst (λ x → (r₁ - (x ⊔ d2 + 1) ≤ 1 → ⊥)) (+-comm d2 1) ¬p)))))
          p5 : suc d2 ≡ l₁
          p5 = subst (λ x → x ≡ l₁) (+-comm d2 1) (proof4' (subst (λ x → d2 ≤ x) (+-comm 1 d2) (n≤1+n d2)) y)
insert' x (node {l = l₁} {r = r₁} n l r p) p1 p2 | yes p₁ | rez2 | fst₁ , fst₂ , inj₂ y , snd₁ | yes p₂ rewrite m≤n⇒m⊔n≡n (<⇒≤ p₁) | n<∞[]⇒[]⊓∞n≡n p1 with l₁ <? r₁ | l₁ >? r₁ 
insert' x (node {l = l₁} {r = r₁} n l r p) p1 p2 | yes p₁ | rez2 | fst₁ , fst₂ , inj₂ y , snd₁ | yes p₂ | no ¬p | no ¬p₁ rewrite x</n,x>/n⇒x≡n ¬p ¬p₁ | ⊔-idem r₁ = suc (fst₁ ⊔ r₁) , (avl n fst₂ r p₂) ,′ inj₂ (cong suc (subst (λ x → x ⊔ r₁ ≡ r₁ + 1) (sym y) (subst (λ x → x ≡ r₁ + 1) (sym (m≥n⇒m⊔n≡m (n≤1+n r₁))) (+-comm 1 r₁))))
insert' x (node {l = l₁} {r = r₁} n l r p) p1 p2 | yes p₁ | rez2 | fst₁ , fst₂ , inj₂ y , snd₁ | yes p₂ | no ¬p | yes p₃ rewrite m≥n⇒m⊔n≡m (<⇒≤ p₃) = suc (fst₁ ⊔ r₁) , (avl n fst₂ r p₂) ,′ inj₂ (cong suc (subst (λ x → x ≡ l₁ + 1) (⊔-comm r₁ fst₁) (proof24 y p₃)))
insert' x (node {l = l₁} {r = r₁} n l r p) p1 p2 | yes p₁ | rez2 | fst₁ , fst₂ , inj₂ y , snd₁ | yes p₂ | yes p₃ | rez rewrite m≤n⇒m⊔n≡n (<⇒≤ p₃) | +-comm r₁ 1 = suc (fst₁ ⊔ r₁) , (avl n fst₂ r p₂) ,′ inj₁ (cong suc (m≤n⇒m⊔n≡n (subst (λ x → x ≤ r₁) (sym y) p₃)))



insert {lower} {upper} {h} x t p1 p2 rewrite n<∞[]⇒[]⊓∞n≡n p1 | []<∞n⇒[]⊔∞n≡n p2 with insert' x t p1 p2
... | .(suc (l₁ ⊔ r₁)) , avl {l = l₁} {r = r₁} n l r p , snd₁ = (l₁ ⊔ r₁ + 1) , (node n l r p) ,′ subst (λ x → x ≡ h ⊎ x ≡ suc h) (+-comm 1 (l₁ ⊔ r₁)) snd₁ ,′ subst (λ x → 1 ≤ x) (+-comm 1 (l₁ ⊔ r₁)) (s≤s z≤n)
... | .(h₁ + 1 + 1) , llRot {h = h₁} n ln t1 t2 t3 , snd₁ = h₁ + 1 + 1 , (leftRotation1 n ln t1 t2 t3) ,′ snd₁ ,′ subst (λ x → 1 ≤ x) (+-comm 1 (h₁ + 1)) (s≤s z≤n)
... | .(h₁ + 1 + 1) , rrRot {h = h₁} n rn t1 t2 t3 , snd₁ = h₁ + 1 + 1 , (rightRotation1 n rn t1 t2 t3) ,′ snd₁ ,′ subst (λ x → 1 ≤ x) (+-comm 1 (h₁ + 1)) (s≤s z≤n)
... | .(h₁ + 1 + 1 + 1) , lrRotL {h = h₁} n ln lrn t1 t2 t3 t4 , snd₁ = h₁ + 1 + 1 + 1 , (leftRightRotationL n ln lrn t1 t2 t3 t4) ,′ snd₁ ,′ subst (λ x → 1 ≤ x) (+-comm 1 (h₁ + 1 + 1)) (s≤s z≤n)
... | .(h₁ + 1 + 1 + 1) , lrRotR {h = h₁} n ln lrn t1 t2 t3 t4 , snd₁ = h₁ + 1 + 1 + 1 , (leftRightRotationR n ln lrn t1 t2 t3 t4) ,′ snd₁ ,′ subst (λ x → 1 ≤ x) (+-comm 1 (h₁ + 1 + 1)) (s≤s z≤n)
... | .(h₁ + 1 + 1 + 1) , rlRotL {h = h₁} n rn rln t1 t2 t3 t4 , snd₁ = h₁ + 1 + 1 + 1 , (rightLeftRotationL n rn rln t1 t2 t3 t4) ,′ snd₁ ,′ subst (λ x → 1 ≤ x) (+-comm 1 (h₁ + 1 + 1)) (s≤s z≤n)
... | .(h₁ + 1 + 1 + 1) , rlRotR {h = h₁} n rn rln t1 t2 t3 t4 , snd₁ = h₁ + 1 + 1 + 1 , (rightLeftRotationR n rn rln t1 t2 t3 t4) ,′ snd₁ ,′ subst (λ x → 1 ≤ x) (+-comm 1 (h₁ + 1 + 1)) (s≤s z≤n)
... | .(h₁ + 1 + 1) , rlRotInit {h = h₁} n rn rln t1 t2 t3 t4 , snd₁ = h₁ + 1 + 1 , (rightLeftRotationInit n rn rln t1 t2 t3 t4) ,′ snd₁ ,′ subst (λ x → 1 ≤ x) (+-comm 1 (h₁ + 1)) (s≤s z≤n)

{-
insert {lower} {upper} {h} x t p1 p2 rewrite n<∞[]⇒[]⊓∞n≡n p1 | []<∞n⇒[]⊔∞n≡n p2 with insert' x t p1 p2
... | .(suc (l₁ ⊔ r₁)) , avl {l = l₁} {r = r₁} n l r p , snd₁ = (l₁ ⊔ r₁ + 1) , (node n l r p) ,′ subst (λ x → x ≡ h ⊎ x ≡ suc h) (+-comm 1 (l₁ ⊔ r₁)) snd₁ ,′ subst (λ x → 1 ≤ x) (+-comm 1 (l₁ ⊔ r₁)) (s≤s z≤n)
... | .(suc (suc (suc _))) , llRot n ln t1 t2 t3 , snd₁ = {!   !}
... | .(suc (suc (suc _))) , rrRot n rn t1 t2 t3 , snd₁ = {!   !}
... | .(suc (suc (suc (suc _)))) , lrRotL n ln lrn x₁ x₂ x₃ x₄ , snd₁ = {!   !}
... | .(suc (suc (suc (suc _)))) , lrRotR n ln lrn x₁ x₂ x₃ x₄ , snd₁ = {!   !}
... | .(suc (suc (suc (suc _)))) , rlRotL n rn rln x₁ x₂ x₃ x₄ , snd₁ = {!   !}
... | .(suc (suc (suc (suc _)))) , rlRotR n rn rln x₁ x₂ x₃ x₄ , snd₁ = {!   !}
-}

{-
insert : {lower upper : ℕ∞} {h : ℕ} → (x : ℕ) → Avl ℕ lower upper h → (p1 : lower <∞ [ x ]) → (p2 : [ x ] <∞ upper) → Σ[ h' ∈ ℕ ] ((Avl ℕ ([ x ] ⊓∞ lower) ([ x ] ⊔∞ upper) h') × ((h' ≡ h) ⊎ (h' ≡ suc h)) × (0 < h'))

insert' : {lower upper : ℕ∞} {h : ℕ} → (x : ℕ) → Avl ℕ lower upper h → (p1 : lower <∞ [ x ]) → (p2 : [ x ] <∞ upper) → InsertTree lower upper
insert' x (empty p) p1 p2 = avl x (empty p1) (empty p2) z≤n
insert' x (node {l = l₁} {r = r₁} n l r p) p1 p2 with x <? n | x >? n
insert' x (node {l = l₁} {r = r₁} n l r p) p1 p2 | no ¬p | no ¬p₁ rewrite sym (x</n,x>/n⇒x≡n ¬p ¬p₁) = avl {l = l₁} {r = r₁} x l r p
insert' x (node {l = l₁} {r = r₁} n l r p) p1 p2 | no ¬p | yes p₁ with newT
    where newT = insert x r ([]<[] p₁) p2
insert' x (node {l = l₁} {r = r₁} n l r p) p1 p2 | no ¬p | yes p₁ | fst₁ , fst₂ , inj₁ x₁ , snd₁ rewrite m≥n⇒m⊓n≡n (<⇒≤ p₁) | []<∞n⇒[]⊔∞n≡n p2 | sym x₁ = avl n l fst₂ p
insert' x (node {l = l₁} {r = r₁} n l r p) p1 p2 | no ¬p | yes p₁ | fst₁ , fst₂ , inj₂ y , snd₁ with fst₁ - l₁ ≤? 1
insert' x (node {l = l₁} {r = r₁} n l r p) p1 p2 | no ¬p | yes p₁ | .(d1 ⊔ d2 + 1) , node {l = d1} {r = d2} n₁ fst₂ fst₃ x₁ , inj₂ y , snd₁ | no ¬p₁ with d2 >? d1
insert' x (node {l = l₁} {r = r₁} n l r p) p1 p2 | no ¬p | yes p₁ | .(d1 ⊔ d2 + _) , node {l = d1} {r = d2} n₁ fst₂ fst₃ x₁ , inj₂ y , snd₁ | no ¬p₁ | false because proof₁ = {!   !}
insert' x (node {l = l₁} {r = r₁} n l r p) p1 p2 | no ¬p | yes p₁ | .(d1 ⊔ d2 + _) , node {l = d1} {r = d2} n₁ fst₂ fst₃ x₁ , inj₂ y , snd₁ | no ¬p₁ | yes p₂ rewrite m≥n⇒m⊓n≡n (<⇒≤ p₁) | []<∞n⇒[]⊔∞n≡n p2 = {! rrRot n n₁ l fst₂ fst₃  !}
insert' x (node {l = l₁} {r = r₁} n l r p) p1 p2 | no ¬p | yes p₁ | fst₁ , fst₂ , inj₂ y , snd₁ | yes p₂ rewrite m≥n⇒m⊓n≡n (<⇒≤ p₁) | []<∞n⇒[]⊔∞n≡n p2 = avl n l fst₂ p₂
insert' x (node {l = l₁} {r = r₁} n l r p) p1 p2 | yes p₁ | rez2 = {!   !}


insert x t p1 p2 rewrite n<∞[]⇒[]⊓∞n≡n p1 | []<∞n⇒[]⊔∞n≡n p2 with insert' x t p1 p2
... | avl {l = l₁} {r = r₁} n l r p rewrite +-comm (l₁ ⊔ r₁) 1 = (l₁ ⊔ r₁ + 1) , (node n l r p) ,′ {!   !} ,′ subst (λ x → 1 ≤ x) (+-comm 1 (l₁ ⊔ r₁)) (s≤s z≤n)
... | llRot n ln x₁ x₂ x₃ = {!   !}
... | rrRot n rn t1 t2 t3 = {!   !}
... | lrRotL n ln lrn x₁ x₂ x₃ x₄ = {!   !}
... | lrRotR n ln lrn x₁ x₂ x₃ x₄ = {!   !}
... | rlRotL n rn rln x₁ x₂ x₃ x₄ = {!   !}
... | rlRotR n rn rln x₁ x₂ x₃ x₄ = {!   !}
-}

--(node n (subst (λ y → Avl ℕ y [ x ] l₁) (sym (n<∞[]⇒[]⊓∞n≡n p1)) l) (subst (λ y → Avl ℕ [ x ] y r₁) (sym ([]<∞n⇒[]⊔∞n≡n p2)) r) p) ,′ ? ,′ ?

{-
insert : {lower upper : ℕ∞} {h : ℕ} → (x : ℕ) → Avl ℕ lower upper h → (p1 : lower <∞ [ x ]) → (p2 : [ x ] <∞ upper) → (Avl ℕ ([ x ] ⊓∞ lower) ([ x ] ⊔∞ upper) h) ⊎ (Avl ℕ ([ x ] ⊓∞ lower) ([ x ] ⊔∞ upper) (suc h))


insert' : {lower upper : ℕ∞} {h : ℕ} → (x : ℕ) → Avl ℕ lower upper h → (p1 : lower <∞ [ x ]) → (p2 : [ x ] <∞ upper) → InsertTree lower upper
insert' x (empty p) p1 p2 = avl x (empty p1) (empty p2) z≤n
insert' x (node {l = l₁} {r = r₁} n l r p) p1 p2 with x <? n | x >? n
insert' x (node {l = l₁} {r = r₁} n l r p) p1 p2 | no ¬p | no ¬p₁ rewrite sym (x</n,x>/n⇒x≡n ¬p ¬p₁) = avl {l = l₁} {r = r₁} x l r p
insert' x (node {l = l₁} {r = r₁} n l r p) p1 p2 | false because proof₁ | yes p₁ with newT
    where newT = insert x r ([]<[] p₁) p2
insert' x (node {l = l₁} {r = r₁} n l r p) p1 p2 | false because proof₁ | yes p₁ | inj₁ x1 with (depth x1) - (depth l) ≤? 1
insert' x (node {l = l₁} {r = r₁} n l r p) p1 p2 | false because proof₁ | yes p₁ | inj₁ x1 | no ¬p with isRightLeaning x1 | isLeftLeaning x1 
insert' x (node {l = l₁} {r = r₁} n l r p) p1 p2 | false because proof₁ | yes p₁ | inj₁ x1 | no ¬p | false | rez2 = {!   !}
insert' x (node {l = l₁} {r = r₁} n l r p) p1 p2 | false because proof₁ | yes p₁ | inj₁ x1 | no ¬p | true | rez2 = {!   !}
insert' x (node {l = l₁} {r = r₁} n l r p) p1 p2 | false because proof₁ | yes p₁ | inj₁ x1 | true because proof₂ rewrite m≥n⇒m⊓n≡n (<⇒≤ p₁) | []<∞n⇒[]⊔∞n≡n p2 = avl n l x1 p
insert' x (node {l = l₁} {r = r₁} n l r p) p1 p2 | false because proof₁ | yes p₁ | inj₂ y1 = {!   !}
insert' x (node {l = l₁} {r = r₁} n l r p) p1 p2 | yes p₁ | rez2 = {!   !}




insert x (empty p) p1 p2 = inj₂ (node x (empty (proof9 p1)) (empty ([]<∞n⇒[]<∞[]⊔∞n p2)) z≤n)
insert {lower} {upper} {h} x (node {l = l₁} {r = r₁} n l r p) p1 p2 with compare x n
... | Data.Nat.less .x k = {!   !} --insert into left, compare l₁ with r₁; with (isAvl (insert2 x l)) --insert2 returns a non-avl tree
... | Data.Nat.equal .x = inj₁ (node n (subst (λ y → Avl ℕ y [ x ] l₁) (sym (n<∞[]⇒[]⊓∞n≡n p1)) l) (subst (λ y → Avl ℕ [ x ] y r₁) (sym ([]<∞n⇒[]⊔∞n≡n p2)) r) p)
... | Data.Nat.greater .n k = {!   !}
-}

--subst (λ y → Avl ℕ y [ x ] h) (sym (n<∞[]⇒[]⊓∞n≡n p1)) l

test2 : Avl ℕ -∞ +∞ 2
test2 = node 5 (node 3 (empty -∞<n) (empty ([]<[] (s≤s (s≤s (s≤s (s≤s z≤n)))))) z≤n) 
               (empty n<+∞) (s≤s z≤n)

insertTest : Avl ℕ -∞ +∞ 2
insertTest = proj₁ (snd (insert 1 test2 -∞<n n<+∞))

--insertTest2 : Avl ℕ -∞ +∞ 2
--insertTest2 = proj₁ (snd (insert 4 test2 -∞<n n<+∞))



               