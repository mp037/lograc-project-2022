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
open Eq using (_≡_; refl; sym; trans; cong; subst; resp; _≢_)
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

leftRightRotationInit : {lower upper : ℕ∞} {h : ℕ}
                    → (n ln lrn : ℕ)
                    → (t1 : Avl ℕ lower [ ln ] h)
                    → (t2 : Avl ℕ [ ln ] [ lrn ] h)
                    → (t3 : Avl ℕ [ lrn ] [ n ] h)
                    → (t4 : Avl ℕ [ n ] upper h)
                    → Avl ℕ lower upper (h + 1 + 1)
leftRightRotationInit {lower} {upper} {h} n ln lrn t1 t2 t3 t4 = subst (Avl ℕ lower upper) (subst (λ x → x + 1 ≡ h + 1 + 1) (sym (⊔-idem (h ⊔ h + 1))) (subst (λ x → x + 1 + 1 ≡ h + 1 + 1) (sym (⊔-idem h)) refl)) (node lrn (node ln t1 t2 (proof31 {h})) (node n t3 t4 (proof31 {h})) (proof31 {h ⊔ h + 1}))

rightRotation : {lower upper : ℕ∞} {h : ℕ} → AlmostAvlLeft ℕ lower upper h → Avl ℕ lower upper (h -ᴺ 1)
rightRotation {lower} (almostleftnode {l = l₁} {r = r₁} n (leftheavynode {l = l₂} {r = r₂} ln ll lr lx) r x) rewrite proof1 (l₂ + 1) | sym (proof6,2 x lx) 
    = node {l = l₂} {r = r₂ ⊔ r₁ + 1} ln (subst (Avl ℕ lower [ ln ]) (proof6,2 x lx) ll) (node n lr r (proof8 x lx)) (proof10 x lx)


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


proof27,0 : ∀ {m n} → m ≡ suc n → ¬ m ≡ n
proof27,0 {m} {n} p rewrite p = 1+n≢n


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

{-
insert : {lower upper : ℕ∞} {h : ℕ} 
        → (x : ℕ) 
        → Avl ℕ lower upper h 
        → (p1 : lower <∞ [ x ]) 
        → (p2 : [ x ] <∞ upper) 
        → Σ[ h' ∈ ℕ ] ((Avl ℕ ([ x ] ⊓∞ lower) ([ x ] ⊔∞ upper) h') × ((h' ≡ h) ⊎ (h' ≡ suc h)) × (0 < h'))

insert' : {lower upper : ℕ∞} {h : ℕ} 
        → (x : ℕ) 
        → Avl ℕ lower upper h 
        → (p1 : lower <∞ [ x ]) 
        → (p2 : [ x ] <∞ upper) 
        → Σ[ h' ∈ ℕ ] ((InsertTree lower upper h') × ((h' ≡ h) ⊎ (h' ≡ suc h)))
insert' x (empty p) p1 p2 = 1 , (avl x (empty p1) (empty p2) z≤n) ,′ inj₂ refl
insert' x (node {l = l₁} {r = r₁} n l r p) p1 p2 with x <? n | x >? n --? n | x >? n
insert' x (node {l = l₁} {r = r₁} n l r p) p1 p2 | no ¬p | no ¬p₁ rewrite sym (x</n,x>/n⇒x≡n ¬p ¬p₁) = (l₁ ⊔ r₁) + 1 , avl {l = l₁} {r = r₁} x l r p ,′ inj₁ refl --(avl {l = l₁} {r = r₁} x l r p) ,′ inj₁ (+-comm 1 (l₁ ⊔ r₁))
insert' x (node {l = l₁} {r = r₁} n l r p) p1 p2 | no ¬p | yes p₁ with newT
    where newT = insert x r ([]<[] p₁) p2 -- inserting in the right subtree
insert' x (node {l = l₁} {r = r₁} n l r p) p1 p2 | no ¬p | yes p₁ | fst₁ , fst₂ , inj₁ x₁ , snd₁ rewrite m≥n⇒m⊓n≡n (<⇒≤ p₁) | []<∞n⇒[]⊔∞n≡n p2 | sym x₁ = (l₁ ⊔ fst₁) + 1 , avl n l fst₂ p ,′ inj₁ refl --(avl n l fst₂ p) ,′ inj₁ (+-comm 1 (l₁ ⊔ fst₁))
insert' x (node {l = l₁} {r = r₁} n l r p) p1 p2 | no ¬p | yes p₁ | fst₁ , fst₂ , inj₂ y , snd₁ with fst₁ - l₁ ≤? 1 --? 1
insert' x (node {l = l₁} {r = r₁} n l r p) p1 p2 | no ¬p | yes p₁ | .(d1 ⊔ d2 + 1) , node {l = d1} {r = d2} n₁ fst₂ fst₃ x₁ , inj₂ y , snd₁ | no ¬p₁ with d2 >? d1 | d2 <? d1 --check if rightLeaning
insert' x (node {l = l₁} {r = r₁} n l r p) p1 p2 | no ¬p | yes p₁ | .(d1 ⊔ d2 + 1) , node {l = d1} {r = d2} n₁ fst₂ fst₃ x₁ , inj₂ y , snd₁ | no ¬p₁ | no ¬p₂ | no ¬p₃ = {!   !}
--insert' x (node {l = l₁} {r = r₁} n l r p) p1 p2 | no ¬p | yes p₁ | .(zero ⊔ d2 + _) , node {l = .zero} {r = d2} n₁ (empty p₂) fst₃ x₁ , inj₂ y , snd₁ | no ¬p₁ | no ¬p₂ | rez2 = contradiction (proof30 (≰⇒> (subst (λ x → ((x + 1) - l₁) ≤ 1 → ⊥) (n<1⇒n≡0 (≰⇒> ¬p₂)) ¬p₁))) (<⇒≱  (s≤s (≤-step (proof29 (proof28 y ¬p₂) p))))
--insert' x (node {l = l₁} {r = r₁} n l r p) p1 p2 | no ¬p | yes p₁ | .(ld1 ⊔ ld2 + 1 ⊔ d2 + _) , node {l = .(ld1 ⊔ ld2 + 1)} {r = d2} n₁ (node {l = ld1} {r = ld2} n₂ fst₂ fst₄ x₂) fst₃ x₁ , inj₂ y , snd₁ | no ¬p₁ | no ¬p₂ | no ¬p₃ = {!   !} -- d1=d2
insert' x (node {l = l₁} {r = r₁} n l r p) p1 p2 | no ¬p | yes p₁ | .(ld1 ⊔ ld2 + 1 ⊔ d2 + _) , node {l = .(ld1 ⊔ ld2 + 1)} {r = d2} n₁ (node {l = ld1} {r = ld2} n₂ fst₂ fst₄ x₂) fst₃ x₁ , inj₂ y , snd₁ | no ¬p₁ | no ¬p₂ | yes p₂ with ld2 >? ld1 | ld2 <? ld1
insert' {lower} {upper} x (node {l = l₁} {r = r₁} n l r p) p1 p2 | no ¬p | yes p₁ | .(ld1 ⊔ ld2 + _ ⊔ d2 + _) , node {.(ld1 ⊔ ld2 + _)} {r = d2} n₁ (node {l = ld1} {r = ld2} n₂ fst₂ fst₄ x₂) fst₃ x₁ , inj₂ y , snd₁ | no ¬p₁ | no ¬p₂ | yes p₂ | no ¬p₃ | no ¬p₄ rewrite m≥n⇒m⊓n≡n (<⇒≤ p₁) | []<∞n⇒[]⊔∞n≡n p2 -- ld1=ld2
    = l₁ + 1 + 1 , (rlRotInit n n₁ n₂ l (subst (Avl ℕ [ n ] [ n₂ ]) p9 fst₂) (subst (Avl ℕ [ n₂ ] [ n₁ ]) (sym p8) fst₄) (subst (Avl ℕ [ n₁ ] upper) p10 fst₃)) ,′ inj₁ (cong (λ x → x + 1) (subst (λ x → l₁ + 1 ≡ x) (sym (m≤n⇒m⊔n≡n p11)) (subst (λ x → x ≡ r₁) (+-comm 1 l₁) (sym p3))))
    where p3 : r₁ ≡ suc l₁
          p3 = ∣n-m∣≤1⇒∣suc[n]-m|>1⇒n≡suc[m] p (≰⇒> (subst (λ x → x - l₁ ≤ 1 → ⊥) y ¬p₁))
          p5 : ld2 ≡ ld1
          p5 = x</n,x>/n⇒x≡n ¬p₄ ¬p₃
          p4 : ld1 ⊔ ld2 ≡ ld2
          p4 = m≤n⇒m⊔n≡n (≤-reflexive (sym p5))
          p6 : ld2 ≡ d2
          p6 = suc-injective (subst (λ x → x ≡ suc d2) (+-comm ld2 1) (proof22 (subst (λ x → x ≤ 1) (∣-∣-comm d2 (ld2 + 1)) (subst (λ x → d2 - (x + 1) ≤ 1) p4 x₁)) (subst (λ x → suc d2 ≤ x + 1) p4 p₂)))
          p7 : r₁ ≡ suc ld2
          p7 = suc-injective (sym (subst (λ x → x ≡ suc r₁) (sym (+-comm 1 (suc ld2))) (subst (λ x → x ≡ suc r₁) (sym (+-comm 1 (ld2 + 1))) (subst (λ x → x + 1 ≡ suc r₁) (m≥n⇒m⊔n≡m (subst (λ x → x ≥ d2) (+-comm 1 ld2) (subst (λ x → suc ld2 ≥ x) p6 (n≤1+n ld2)))) (subst (λ x → x + 1 ⊔ d2 + 1 ≡ suc r₁) p4 y)))))
          p8 : l₁ ≡ ld2
          p8 = suc-injective (subst (λ x → x ≡ suc ld2) p3 p7)
          p9 : ld1 ≡ l₁
          p9 rewrite p8 | sym p5 = refl
          p10 : d2 ≡ l₁
          p10 rewrite p8 | sym p6 = refl
          p11 : r₁ ≥ l₁
          p11 rewrite p3 = n≤1+n l₁
insert' {lower} {upper} x (node {l = l₁} {r = r₁} n l r p) p1 p2 | no ¬p | yes p₁ | .(ld1 ⊔ ld2 + _ ⊔ d2 + _) , node {.(ld1 ⊔ ld2 + _)} {r = d2} n₁ (node {l = ld1} {r = ld2} n₂ fst₂ fst₄ x₂) fst₃ x₁ , inj₂ y , snd₁ | no ¬p₁ | no ¬p₂ | yes p₂ | no ¬p₃ | yes p₃ rewrite m≥n⇒m⊓n≡n (<⇒≤ p₁) | []<∞n⇒[]⊔∞n≡n p2
    = ld2 + 1 + 1 + 1 , (rlRotL n n₁ n₂ (subst (Avl ℕ lower [ n ]) p9 l) (subst (Avl ℕ [ n ] [ n₂ ]) (subst (λ x → ld1 ≡ x) (+-comm 1 ld2) p5) fst₂) fst₄ (subst (Avl ℕ [ n₁ ]  upper) p10 fst₃)) ,′ inj₁ (cong (λ x → x + 1) (subst (λ x → ld2 + 1 + 1 ≡ x) (sym (m≤n⇒m⊔n≡n p11)) (subst (λ x → ld2 + 1 + 1 ≡ x) (sym p7) (subst (λ x → ld2 + 1 + 1 ≡ suc x) (sym p5) (subst (λ x → x ≡ suc (suc ld2)) (+-comm 1 (ld2 + 1)) (cong suc (+-comm ld2 1)))))))
    where p3 : r₁ ≡ suc l₁
          p3 = ∣n-m∣≤1⇒∣suc[n]-m|>1⇒n≡suc[m] p (≰⇒> (subst (λ x → x - l₁ ≤ 1 → ⊥) y ¬p₁))
          p4 : ld1 ⊔ ld2 ≡ ld1
          p4 = m≥n⇒m⊔n≡m (<⇒≤ p₃)
          p5 : ld1 ≡ suc ld2
          p5 = proof22 (subst (λ x → x ≤ 1) (∣-∣-comm ld2 ld1) x₂) p₃
          p6 : ld1 ≡ d2
          p6 = suc-injective (subst (λ x → x ≡ suc d2) (+-comm ld1 1) (proof22 (subst (λ x → x ≤ 1) (∣-∣-comm d2 (ld1 + 1)) (subst (λ x → d2 - (x + 1) ≤ 1) p4 x₁)) (subst (λ x → suc d2 ≤ x + 1) p4 p₂)))
          p7 : r₁ ≡ suc ld1
          p7 = suc-injective (sym (subst (λ x → x ≡ suc r₁) (sym (+-comm 1 (suc ld1))) (subst (λ x → x ≡ suc r₁) (sym (+-comm 1 (ld1 + 1))) (subst (λ x → x + 1 ≡ suc r₁) (m≥n⇒m⊔n≡m (subst (λ x → x ≥ d2) (+-comm 1 ld1) (subst (λ x → suc ld1 ≥ x) p6 (n≤1+n ld1)))) (subst (λ x → x + 1 ⊔ d2 + 1 ≡ suc r₁) p4 y)))))
          p8 : l₁ ≡ ld1
          p8 = suc-injective (subst (λ x → x ≡ suc ld1) p3 p7)
          p9 : l₁ ≡ ld2 + 1
          p9 rewrite +-comm ld2 1 | sym p5 = p8
          p10 : d2 ≡ ld2 + 1
          p10 rewrite +-comm ld2 1 = subst (λ x → x ≡ suc ld2) p6 p5
          p11 : r₁ ≥ l₁
          p11 rewrite p3 = n≤1+n l₁
insert' {lower} {upper} x (node {l = l₁} {r = r₁} n l r p) p1 p2 | no ¬p | yes p₁ | .(ld1 ⊔ ld2 + _ ⊔ d2 + _) , node {.(ld1 ⊔ ld2 + _)} {r = d2} n₁ (node {l = ld1} {r = ld2} n₂ fst₂ fst₄ x₂) fst₃ x₁ , inj₂ y , snd₁ | no ¬p₁ | no ¬p₂ | yes p₂ | yes p₃ | rez2 rewrite m≥n⇒m⊓n≡n (<⇒≤ p₁) | []<∞n⇒[]⊔∞n≡n p2
    = ld1 + 1 + 1 + 1 , (rlRotR n n₁ n₂ (subst (Avl ℕ lower [ n ]) p9 l) fst₂ (subst (Avl ℕ [ n₂ ] [ n₁ ]) (subst (λ x → ld2 ≡ x) (+-comm 1 ld1) p5) fst₄) (subst (Avl ℕ [ n₁ ]  upper) p10 fst₃)) ,′ inj₁ (cong (λ x → x + 1) (subst (λ x → ld1 + 1 + 1 ≡ x) (sym (m≤n⇒m⊔n≡n p11)) (subst (λ x → ld1 + 1 + 1 ≡ x) (sym p7) (subst (λ x → ld1 + 1 + 1 ≡ suc x) (sym p5) (subst (λ x → x ≡ suc (suc ld1)) (+-comm 1 (ld1 + 1)) (cong suc (+-comm ld1 1)))))))
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
          p10 : d2 ≡ ld1 + 1
          p10 rewrite +-comm ld1 1 = subst (λ x → x ≡ suc ld1) p6 p5 
          p11 : r₁ ≥ l₁
          p11 rewrite p3 = n≤1+n l₁
insert' x (node {l = l₁} {r = r₁} n l r p) p1 p2 | no ¬p | yes p₁ | .(d1 ⊔ d2 + 1) , node {l = d1} {r = d2} n₁ fst₂ fst₃ x₁ , inj₂ y , snd₁ | no ¬p₁ | yes p₂ | rez rewrite m≥n⇒m⊓n≡n (<⇒≤ p₁) | []<∞n⇒[]⊔∞n≡n p2 | proof27' (proof22 x₁ p₂) p (subst (λ x → x ≡ suc r₁) (+-comm (d1 ⊔ d2) 1) y) p₂ (subst (λ x → (x - l₁ ≤ 1 → ⊥)) (+-comm (d1 ⊔ d2) 1) ¬p₁) | proof27,1 (proof22 x₁ p₂) (proof27' (proof22 x₁ p₂) p (subst (λ x → x ≡ suc r₁) (+-comm (d1 ⊔ d2) 1) y) p₂ (subst (λ x → (x - l₁ ≤ 1 → ⊥)) (+-comm (d1 ⊔ d2) 1) ¬p₁))
    = l₁ + 1 + 1 , (rrRot n n₁ l fst₂ fst₃) ,′ inj₁ (cong (λ x → x + 1) (subst (λ x → l₁ + 1 ≡ x) (sym (m≤n⇒m⊔n≡n (subst (λ x → l₁ ≤ x) (subst (λ x → x ≡ r₁) (m≤n⇒m⊔n≡n (<⇒≤ p₂)) (proof4,0 y)) (subst (λ x → l₁ ≤ x) (sym (proof27,1 (proof22 x₁ p₂) p3)) (subst (λ x → l₁ ≤ x) (+-comm 1 l₁) (n≤1+n l₁)))))) (subst (λ x → l₁ + 1 ≡ x) p4 (subst (λ x → l₁ + 1 ≡ x) (sym p5) (+-comm l₁ 1)))))
    where p3 : d1 ≡ l₁
          p3 = proof27' (proof22 x₁ p₂) p (subst (λ x → x ≡ suc r₁) (+-comm (d1 ⊔ d2) 1) y) p₂ (subst (λ x → (x - l₁ ≤ 1 → ⊥)) (+-comm (d1 ⊔ d2) 1) ¬p₁)
          p4 : d2 ≡ r₁
          p4 = subst (λ x → x ≡ r₁) (m≤n⇒m⊔n≡n (<⇒≤ p₂)) (proof4,0 y)
          p5 : d2 ≡ suc l₁
          p5 = subst (λ x → d2 ≡ suc x) p3 (proof22 x₁ p₂)
insert' x (node {l = l₁} {r = r₁} n l r p) p1 p2 | no ¬p | yes p₁ | fst₁ , fst₂ , inj₂ y , snd₁ | yes p₂ rewrite m≥n⇒m⊓n≡n (<⇒≤ p₁) | []<∞n⇒[]⊔∞n≡n p2 with l₁ <? r₁ | l₁ >? r₁ --? r₁ | l₁ >? r₁
insert' x (node {l = l₁} {r = r₁} n l r p) p1 p2 | no ¬p | yes p₁ | fst₁ , fst₂ , inj₂ y , snd₁ | yes p₂ | no ¬p₁ | no ¬p₂ rewrite sym (x</n,x>/n⇒x≡n ¬p₁ ¬p₂) | ⊔-idem l₁ = (l₁ ⊔ fst₁) + 1 , avl n l fst₂ p₂ ,′ inj₂ (subst (λ x → l₁ ⊔ x + 1 ≡ suc (l₁ + 1)) (sym y) (subst (λ x → x + 1 ≡ suc (l₁ + 1)) (sym (m≤n⇒m⊔n≡n (n≤1+n l₁))) refl)) --(avl n l fst₂ p₂) ,′ inj₂ (cong suc (subst (λ x → l₁ ⊔ x ≡ l₁ + 1) (sym y) (subst (λ x → x ≡ l₁ + 1) (sym (m≤n⇒m⊔n≡n (n≤1+n l₁))) (+-comm 1 l₁)))) 
insert' x (node {l = l₁} {r = r₁} n l r p) p1 p2 | no ¬p | yes p₁ | fst₁ , fst₂ , inj₂ y , snd₁ | yes p₂ | no ¬p₁ | yes p₃ rewrite m≥n⇒m⊔n≡m (<⇒≤ p₃) | +-comm l₁ 1 = (l₁ ⊔ fst₁) + 1 , avl n l fst₂ p₂ ,′ inj₁ (subst (λ x → x ≡ suc l₁) (+-comm 1 (l₁ ⊔ fst₁)) (cong suc (m≥n⇒m⊔n≡m (subst (λ x → l₁ ≥ x) (sym y) p₃)))) --(avl n l fst₂ p₂) ,′ inj₁ (cong suc (m≥n⇒m⊔n≡m (subst (λ x → l₁ ≥ x) (sym y) p₃)))
insert' x (node {l = l₁} {r = r₁} n l r p) p1 p2 | no ¬p | yes p₁ | fst₁ , fst₂ , inj₂ y , snd₁ | yes p₂ | yes p₃ | rez2 rewrite m≤n⇒m⊔n≡n (<⇒≤ p₃) = (l₁ ⊔ fst₁) + 1 , avl n l fst₂ p₂ ,′ inj₂ (subst (λ x → x ≡ suc (r₁ + 1)) (+-comm 1 (l₁ ⊔ fst₁)) (cong suc (proof24 y p₃))) --(avl n l fst₂ p₂) ,′ inj₂ (cong suc (proof24 y p₃))
insert' x (node {l = l₁} {r = r₁} n l r p) p1 p2 | yes p₁ | rez2 with newT --inserting in the left subtree
    where newT = insert x l p1 ([]<[] p₁)
insert' x (node {l = l₁} {r = r₁} n l r p) p1 p2 | yes p₁ | rez2 | fst₁ , fst₂ , inj₁ x₁ , snd₁ rewrite m≤n⇒m⊔n≡n (<⇒≤ p₁) | sym x₁ | n<∞[]⇒[]⊓∞n≡n p1 = (fst₁ ⊔ r₁) + 1 , avl n fst₂ r p ,′ inj₁ refl --(avl n fst₂ r p) ,′ inj₁ (+-comm 1 (fst₁ ⊔ r₁))
insert' x (node {l = l₁} {r = r₁} n l r p) p1 p2 | yes p₁ | rez2 | fst₁ , fst₂ , inj₂ y , snd₁ with r₁ - fst₁ ≤? 1 
insert' x (node {l = l₁} {r = r₁} n l r p) p1 p2 | yes p₁ | rez2 | .(d1 ⊔ d2 + 1) , node {l = d1} {r = d2} n₁ fst₂ fst₃ x₁ , inj₂ y , snd₁ | no ¬p with d1 >? d2 | d1 <? d2 --check if leftLeaning 
insert' x (node {l = l₁} {r = r₁} n l r p) p1 p2 | yes p₁ | rez2 | .(d1 ⊔ zero + _) , node {l = d1} {r = .zero} n₁ fst₂ (empty p₂) x₁ , inj₂ y , snd₁ | no ¬p | no ¬p₁ | rez = contradiction (proof30 (subst (λ x → x > 1) (∣-∣-comm r₁ 1) (≰⇒> (subst (λ x → (r₁ - (x + 1)) ≤ 1 → ⊥) (n<1⇒n≡0 (≰⇒> ¬p₁)) (subst (λ x → (r₁ - (x + 1)) ≤ 1 → ⊥) (m≥n⇒m⊔n≡m z≤n) ¬p))))) (<⇒≱  (s≤s (≤-step (proof29 (proof28 (subst (λ x → x + 1 ≡ suc l₁) (m≥n⇒m⊔n≡m z≤n) y) ¬p₁) (subst (λ x → x ≤ 1) (∣-∣-comm r₁ l₁) p)))))
insert' x (node {l = l₁} {r = r₁} n l r p) p1 p2 | yes p₁ | rez2 | .(d1 ⊔ (rd1 ⊔ rd2 + 1) + _) , node {l = d1} {r = .(rd1 ⊔ rd2 + 1)} n₁ fst₂ (node {l = rd1} {r = rd2} n₂ fst₃ fst₄ x₂) x₁ , inj₂ y , snd₁ | no ¬p | no ¬p₁ | no ¬p₂ = {!   !} -- d1=d2
insert' x (node {l = l₁} {r = r₁} n l r p) p1 p2 | yes p₁ | rez2 | .(d1 ⊔ (rd1 ⊔ rd2 + 1) + _) , node {l = d1} {r = .(rd1 ⊔ rd2 + 1)} n₁ fst₂ (node {l = rd1} {r = rd2} n₂ fst₃ fst₄ x₂) x₁ , inj₂ y , snd₁ | no ¬p | no ¬p₁ | yes p₂ with rd1 >? rd2 | rd1 <? rd2 
insert' {lower} {upper} x (node {l = l₁} {r = r₁} n l r p) p1 p2 | yes p₁ | rez2 | .(d1 ⊔ (rd1 ⊔ rd2 + _) + _) , node {l = d1} {.(rd1 ⊔ rd2 + _)} n₁ fst₂ (node {l = rd1} {r = rd2} n₂ fst₃ fst₄ x₂) x₁ , inj₂ y , snd₁ | no ¬p | no ¬p₁ | yes p₂ | no ¬p₂ | no ¬p₃ rewrite m≤n⇒m⊔n≡n (<⇒≤ p₁) | n<∞[]⇒[]⊓∞n≡n p1
    = r₁ + 1 + 1 , (lrRotInit n n₁ n₂ (subst (Avl ℕ lower [ n₁ ]) (p10) fst₂) (subst (Avl ℕ [ n₁ ] [ n₂ ]) (sym p8) fst₃) (subst (Avl ℕ [ n₂ ] [ n ]) p9 fst₄) r) ,′ inj₁ (cong (λ x → x + 1) (subst (λ x → r₁ + 1 ≡ x) (sym (m≥n⇒m⊔n≡m p11)) (subst (λ x → x ≡ l₁) (+-comm 1 r₁) (sym p3))))
    where p3 : l₁ ≡ suc r₁
          p3 = ∣n-m∣≤1⇒∣suc[n]-m|>1⇒n≡suc[m] (subst (λ x → x ≤ 1) (∣-∣-comm r₁ l₁) p) (≰⇒> (subst (λ x → x ≤ 1 → ⊥) (∣-∣-comm r₁ (suc l₁)) (subst (λ x → r₁ - x ≤ 1 → ⊥) y ¬p)))
          p5 : rd1 ≡ rd2
          p5 = x</n,x>/n⇒x≡n ¬p₃ ¬p₂
          p4 : rd1 ⊔ rd2 ≡ rd1
          p4 = m≥n⇒m⊔n≡m (≤-reflexive (sym p5))
          p6 : rd1 ≡ d1
          p6 = suc-injective (subst (λ x → x ≡ suc d1) (+-comm rd1 1) (proof22 (subst (λ x → x ≤ 1) (∣-∣-comm d1 (rd1 + 1)) (subst (λ x → d1 - (x + 1) ≤ 1) p4 (subst (λ x → x ≤ 1) (∣-∣-comm (rd1 ⊔ rd2 + 1) d1) x₁))) (subst (λ x → suc d1 ≤ x + 1) p4 p₂)))
          p7 : l₁ ≡ suc rd1
          p7 = suc-injective (sym (subst (λ x → x ≡ suc l₁) (sym (+-comm 1 (suc rd1))) (subst (λ x → x ≡ suc l₁) (sym (+-comm 1 (rd1 + 1))) (subst (λ x → x + 1 ≡ suc l₁) (m≥n⇒m⊔n≡m (subst (λ x → x ≥ d1) (+-comm 1 rd1) (subst (λ x → suc rd1 ≥ x) p6 (n≤1+n rd1)))) (subst (λ x → x + 1 ⊔ d1 + 1 ≡ suc l₁) p4 (subst (λ x → x + 1 ≡ suc l₁) (⊔-comm d1 (rd1 ⊔ rd2 + 1)) y))))))
          p8 : r₁ ≡ rd1
          p8 = suc-injective (subst (λ x → x ≡ suc rd1) p3 p7)
          p9 : rd2 ≡ r₁
          p9 rewrite p8 | sym p5 = refl
          p10 : d1 ≡ r₁
          p10 rewrite p8 | sym p6 = refl
          p11 : l₁ ≥ r₁
          p11 rewrite p3 = n≤1+n r₁
insert' {lower} {upper} x (node {l = l₁} {r = r₁} n l r p) p1 p2 | yes p₁ | rez2 | .(d1 ⊔ (rd1 ⊔ rd2 + _) + _) , node {l = d1} {.(rd1 ⊔ rd2 + _)} n₁ fst₂ (node {l = rd1} {r = rd2} n₂ fst₃ fst₄ x₂) x₁ , inj₂ y , snd₁ | no ¬p | no ¬p₁ | yes p₂ | no ¬p₂ | yes p₃ rewrite m≤n⇒m⊔n≡n (<⇒≤ p₁) | n<∞[]⇒[]⊓∞n≡n p1
    = rd1 + 1 + 1 + 1 , (lrRotR n n₁ n₂ (subst (Avl ℕ lower [ n₁ ]) p10 fst₂) fst₃ (subst (Avl ℕ [ n₂ ] [ n ]) (subst (λ x → rd2 ≡ x) (+-comm 1 rd1) p5) fst₄) (subst (Avl ℕ [ n ] upper) p9 r)) ,′ inj₁ (cong (λ x → x + 1) (subst (λ x → rd1 + 1 + 1 ≡ x) (sym (m≥n⇒m⊔n≡m p11)) (subst (λ x → rd1 + 1 + 1 ≡ x) (sym p3) (subst (λ x → rd1 + 1 + 1 ≡ x) (+-comm r₁ 1) (subst (λ x → rd1 + 1 + 1 ≡ x + 1) (sym p9) refl)))))
    where p3 : l₁ ≡ suc r₁
          p3 = ∣n-m∣≤1⇒∣suc[n]-m|>1⇒n≡suc[m] (subst (λ x → x ≤ 1) (∣-∣-comm r₁ l₁) p) (≰⇒> (subst (λ x → x ≤ 1 → ⊥) (∣-∣-comm r₁ (suc l₁)) (subst (λ x → r₁ - x ≤ 1 → ⊥) y ¬p)))
          p4 : rd1 ⊔ rd2 ≡ rd2
          p4 = m≤n⇒m⊔n≡n (<⇒≤ p₃)
          p5 : rd2 ≡ suc rd1
          p5 = proof22 x₂ p₃
          p6 : rd2 ≡ d1
          p6 = suc-injective (subst (λ x → x ≡ suc d1) (+-comm rd2 1) (proof22 (subst (λ x → x ≤ 1) (∣-∣-comm d1 (rd2 + 1)) (subst (λ x → d1 - (x + 1) ≤ 1) p4 (subst (λ x → x ≤ 1) (∣-∣-comm (rd1 ⊔ rd2 + 1) d1) x₁))) (subst (λ x → suc d1 ≤ x + 1) p4 p₂)))
          p7 : l₁ ≡ suc rd2
          p7 = suc-injective (sym (subst (λ x → x ≡ suc l₁) (sym (+-comm 1 (suc rd2))) (subst (λ x → x ≡ suc l₁) (sym (+-comm 1 (rd2 + 1))) (subst (λ x → x + 1 ≡ suc l₁) (m≤n⇒m⊔n≡n (subst (λ x → x ≥ d1) (+-comm 1 rd2) (subst (λ x → suc rd2 ≥ x) p6 (n≤1+n rd2)))) (subst (λ x → d1 ⊔ (x + 1) + 1 ≡ suc l₁) p4 (subst (λ x → x + 1 ≡ suc l₁) (⊔-comm (rd1 ⊔ rd2 + 1) d1) (subst (λ x → x + 1 ≡ suc l₁) (⊔-comm d1 (rd1 ⊔ rd2 + 1)) y)))))))
          p8 : r₁ ≡ rd2
          p8 = suc-injective (subst (λ x → x ≡ suc rd2) p3 p7)
          p9 : r₁ ≡ rd1 + 1
          p9 rewrite +-comm rd1 1 | sym p5 = p8
          p10 : d1 ≡ rd1 + 1
          p10 rewrite +-comm rd1 1 = subst (λ x → x ≡ suc rd1) p6 p5
          p11 : l₁ ≥ r₁
          p11 rewrite p3 = n≤1+n r₁
insert' {lower} {upper} x (node {l = l₁} {r = r₁} n l r p) p1 p2 | yes p₁ | rez2 | .(d1 ⊔ (rd1 ⊔ rd2 + _) + _) , node {l = d1} {.(rd1 ⊔ rd2 + _)} n₁ fst₂ (node {l = rd1} {r = rd2} n₂ fst₃ fst₄ x₂) x₁ , inj₂ y , snd₁ | no ¬p | no ¬p₁ | yes p₂ | yes p₃ | rez3 rewrite m≤n⇒m⊔n≡n (<⇒≤ p₁) | n<∞[]⇒[]⊓∞n≡n p1
    = rd2 + 1 + 1 + 1 , (lrRotL n n₁ n₂ (subst (Avl ℕ lower [ n₁ ]) p10 fst₂) (subst (Avl ℕ [ n₁ ] [ n₂ ]) (subst (λ x → rd1 ≡ x) (+-comm 1 rd2) p5) fst₃) fst₄ (subst (Avl ℕ [ n ] upper) p9 r)) ,′ inj₁ (cong (λ x → x + 1) (subst (λ x → rd2 + 1 + 1 ≡ x) (sym (m≥n⇒m⊔n≡m p11)) (subst (λ x → rd2 + 1 + 1 ≡ x) (sym p3) (subst (λ x → rd2 + 1 + 1 ≡ x) (+-comm r₁ 1) (subst (λ x → rd2 + 1 + 1 ≡ x + 1) (sym p9) refl)))))
    where p3 : l₁ ≡ suc r₁
          p3 = ∣n-m∣≤1⇒∣suc[n]-m|>1⇒n≡suc[m] (subst (λ x → x ≤ 1) (∣-∣-comm r₁ l₁) p) (≰⇒> (subst (λ x → x ≤ 1 → ⊥) (∣-∣-comm r₁ (suc l₁)) (subst (λ x → r₁ - x ≤ 1 → ⊥) y ¬p)))
          p4 : rd1 ⊔ rd2 ≡ rd1
          p4 = m≥n⇒m⊔n≡m (<⇒≤ p₃)
          p5 : rd1 ≡ suc rd2
          p5 = proof22 (subst (λ x → x ≤ 1) (∣-∣-comm rd2 rd1) x₂) p₃
          p6 : rd1 ≡ d1
          p6 = suc-injective (subst (λ x → x ≡ suc d1) (+-comm rd1 1) (proof22 (subst (λ x → x ≤ 1) (∣-∣-comm d1 (rd1 + 1)) (subst (λ x → d1 - (x + 1) ≤ 1) p4 (subst (λ x → x ≤ 1) (∣-∣-comm (rd1 ⊔ rd2 + 1) d1) x₁))) (subst (λ x → suc d1 ≤ x + 1) p4 p₂)))
          p7 : l₁ ≡ suc rd1
          p7 = suc-injective (sym (subst (λ x → x ≡ suc l₁) (sym (+-comm 1 (suc rd1))) (subst (λ x → x ≡ suc l₁) (sym (+-comm 1 (rd1 + 1))) (subst (λ x → x + 1 ≡ suc l₁) (m≤n⇒m⊔n≡n (subst (λ x → x ≥ d1) (+-comm 1 rd1) (subst (λ x → suc rd1 ≥ x) p6 (n≤1+n rd1)))) (subst (λ x → d1 ⊔ (x + 1) + 1 ≡ suc l₁) p4 (subst (λ x → x + 1 ≡ suc l₁) (⊔-comm (rd1 ⊔ rd2 + 1) d1) (subst (λ x → x + 1 ≡ suc l₁) (⊔-comm d1 (rd1 ⊔ rd2 + 1)) y)))))))
          p8 : r₁ ≡ rd1
          p8 = suc-injective (subst (λ x → x ≡ suc rd1) p3 p7)
          p9 : r₁ ≡ rd2 + 1
          p9 rewrite +-comm rd2 1 | sym p5 = p8
          p10 : d1 ≡ rd2 + 1
          p10 rewrite +-comm rd2 1 = subst (λ x → x ≡ suc rd2) p6 p5
          p11 : l₁ ≥ r₁
          p11 rewrite p3 = n≤1+n r₁
insert' {lower} {upper} x (node {l = l₁} {r = r₁} n l r p) p1 p2 | yes p₁ | rez2 | .(d1 ⊔ d2 + _) , node {l = d1} {r = d2} n₁ fst₂ fst₃ x₁ , inj₂ y , snd₁ | no ¬p | yes p₂ | rez rewrite m≤n⇒m⊔n≡n (<⇒≤ p₁) | proof22 (subst (λ x → x ≤ 1) (∣-∣-comm d2 d1) x₁) p₂ | +-comm 1 d2 | n<∞[]⇒[]⊓∞n≡n p1
    = d2 + 1 + 1 , (llRot n n₁ fst₂ fst₃ (subst (Avl ℕ [ n ] upper) (sym p3) r)) ,′ inj₁ (cong (λ x → x + 1) (subst (λ x → x ≡ l₁ ⊔ r₁) (+-comm 1 d2) (subst (λ x → x ≡ l₁ ⊔ r₁) (sym p5) (sym (m≥n⇒m⊔n≡m (subst (λ x → l₁ ≥ x) p3 (subst (λ x → x ≥ d2) p5 (n≤1+n d2))))))))
    where p4 : d1 ≡ suc d2
          p4 = proof22 (subst (λ x → x ≤ 1) (∣-∣-comm d2 d1) x₁) (subst (λ x → x ≤ d1) (+-comm d2 1) p₂) 
          p3 : d2 ≡ r₁
          p3 = proof27' p4 (subst (λ x → x ≤ 1) (∣-∣-comm r₁ l₁) p) (subst (λ x → x ≡ suc l₁) (+-comm (d2 ⊔ d1) 1) (subst (λ x → d2 ⊔ x + 1 ≡ suc l₁) (sym p4) (subst (λ x → d2 ⊔ x + 1 ≡ suc l₁) (+-comm d2 1) (subst (λ x → x + 1 ≡ suc l₁) (⊔-comm (d2 + 1) d2) y)))) (subst (λ x → x ≤ d1) (+-comm d2 1) p₂) (subst (λ x → (x ≤ 1 → ⊥)) (∣-∣-comm r₁ (suc (d2 ⊔ d1))) (subst (λ x → (r₁ - x ≤ 1 → ⊥)) (+-comm (d2 ⊔ d1) 1) (subst (λ x → (r₁ - (x + 1) ≤ 1 → ⊥)) (⊔-comm d1 d2) (subst (λ x → (r₁ - (x ⊔ d2 + 1) ≤ 1 → ⊥)) (sym p4) (subst (λ x → (r₁ - (x ⊔ d2 + 1) ≤ 1 → ⊥)) (+-comm d2 1) ¬p)))))
          p5 : suc d2 ≡ l₁
          p5 = subst (λ x → x ≡ l₁) (+-comm d2 1) (proof4' (subst (λ x → d2 ≤ x) (+-comm 1 d2) (n≤1+n d2)) y)
insert' x (node {l = l₁} {r = r₁} n l r p) p1 p2 | yes p₁ | rez2 | fst₁ , fst₂ , inj₂ y , snd₁ | yes p₂ rewrite m≤n⇒m⊔n≡n (<⇒≤ p₁) | n<∞[]⇒[]⊓∞n≡n p1 with l₁ <? r₁ | l₁ >? r₁ 
insert' x (node {l = l₁} {r = r₁} n l r p) p1 p2 | yes p₁ | rez2 | fst₁ , fst₂ , inj₂ y , snd₁ | yes p₂ | no ¬p | no ¬p₁ rewrite x</n,x>/n⇒x≡n ¬p ¬p₁ | ⊔-idem r₁ = (fst₁ ⊔ r₁) + 1 , avl n fst₂ r p₂ ,′ inj₂ (subst (λ x → x ≡ suc (r₁ + 1)) (+-comm 1 (fst₁ ⊔ r₁)) (cong suc (subst (λ x → x ⊔ r₁ ≡ r₁ + 1) (sym y) (subst (λ x → x ≡ r₁ + 1) (sym (m≥n⇒m⊔n≡m (n≤1+n r₁))) (+-comm 1 r₁))))) --(avl n fst₂ r p₂) ,′ inj₂ (cong suc (subst (λ x → x ⊔ r₁ ≡ r₁ + 1) (sym y) (subst (λ x → x ≡ r₁ + 1) (sym (m≥n⇒m⊔n≡m (n≤1+n r₁))) (+-comm 1 r₁))))
insert' x (node {l = l₁} {r = r₁} n l r p) p1 p2 | yes p₁ | rez2 | fst₁ , fst₂ , inj₂ y , snd₁ | yes p₂ | no ¬p | yes p₃ rewrite m≥n⇒m⊔n≡m (<⇒≤ p₃) = (fst₁ ⊔ r₁) + 1 , avl n fst₂ r p₂ ,′ inj₂ (subst (λ x → x ≡ suc (l₁ + 1)) (+-comm 1 (fst₁ ⊔ r₁)) (cong suc (subst (λ x → x ≡ l₁ + 1) (⊔-comm r₁ fst₁) (proof24 y p₃)))) --(avl n fst₂ r p₂) ,′ inj₂ (cong suc (subst (λ x → x ≡ l₁ + 1) (⊔-comm r₁ fst₁) (proof24 y p₃)))
insert' x (node {l = l₁} {r = r₁} n l r p) p1 p2 | yes p₁ | rez2 | fst₁ , fst₂ , inj₂ y , snd₁ | yes p₂ | yes p₃ | rez rewrite m≤n⇒m⊔n≡n (<⇒≤ p₃) | +-comm r₁ 1 = (fst₁ ⊔ r₁) + 1 , avl n fst₂ r p₂ ,′ inj₁ (subst (λ x → x ≡ suc r₁) (+-comm 1 (fst₁ ⊔ r₁)) (cong suc (m≤n⇒m⊔n≡n (subst (λ x → x ≤ r₁) (sym y) p₃)))) --(avl n fst₂ r p₂) ,′ inj₁ (cong suc (m≤n⇒m⊔n≡n (subst (λ x → x ≤ r₁) (sym y) p₃)))



insert {lower} {upper} {h} x t p1 p2 rewrite n<∞[]⇒[]⊓∞n≡n p1 | []<∞n⇒[]⊔∞n≡n p2 with insert' x t p1 p2
... | .((l₁ ⊔ r₁) + 1) , avl {l = l₁} {r = r₁} n l r p , snd₁ = (l₁ ⊔ r₁ + 1) , (node n l r p) ,′ snd₁ ,′ subst (λ x → 1 ≤ x) (+-comm 1 (l₁ ⊔ r₁)) (s≤s z≤n) --subst (λ x → x ≡ h ⊎ x ≡ suc h) (+-comm 1 (l₁ ⊔ r₁)) snd₁
... | .(h₁ + 1 + 1) , llRot {h = h₁} n ln t1 t2 t3 , snd₁ = h₁ + 1 + 1 , (leftRotation1 n ln t1 t2 t3) ,′ snd₁ ,′ subst (λ x → 1 ≤ x) (+-comm 1 (h₁ + 1)) (s≤s z≤n)
... | .(h₁ + 1 + 1) , rrRot {h = h₁} n rn t1 t2 t3 , snd₁ = h₁ + 1 + 1 , (rightRotation1 n rn t1 t2 t3) ,′ snd₁ ,′ subst (λ x → 1 ≤ x) (+-comm 1 (h₁ + 1)) (s≤s z≤n)
... | .(h₁ + 1 + 1 + 1) , lrRotL {h = h₁} n ln lrn t1 t2 t3 t4 , snd₁ = h₁ + 1 + 1 + 1 , (leftRightRotationL n ln lrn t1 t2 t3 t4) ,′ snd₁ ,′ subst (λ x → 1 ≤ x) (+-comm 1 (h₁ + 1 + 1)) (s≤s z≤n)
... | .(h₁ + 1 + 1 + 1) , lrRotR {h = h₁} n ln lrn t1 t2 t3 t4 , snd₁ = h₁ + 1 + 1 + 1 , (leftRightRotationR n ln lrn t1 t2 t3 t4) ,′ snd₁ ,′ subst (λ x → 1 ≤ x) (+-comm 1 (h₁ + 1 + 1)) (s≤s z≤n)
... | .(h₁ + 1 + 1 + 1) , rlRotL {h = h₁} n rn rln t1 t2 t3 t4 , snd₁ = h₁ + 1 + 1 + 1 , (rightLeftRotationL n rn rln t1 t2 t3 t4) ,′ snd₁ ,′ subst (λ x → 1 ≤ x) (+-comm 1 (h₁ + 1 + 1)) (s≤s z≤n)
... | .(h₁ + 1 + 1 + 1) , rlRotR {h = h₁} n rn rln t1 t2 t3 t4 , snd₁ = h₁ + 1 + 1 + 1 , (rightLeftRotationR n rn rln t1 t2 t3 t4) ,′ snd₁ ,′ subst (λ x → 1 ≤ x) (+-comm 1 (h₁ + 1 + 1)) (s≤s z≤n)
... | .(h₁ + 1 + 1) , rlRotInit {h = h₁} n rn rln t1 t2 t3 t4 , snd₁ = h₁ + 1 + 1 , (rightLeftRotationInit n rn rln t1 t2 t3 t4) ,′ snd₁ ,′ subst (λ x → 1 ≤ x) (+-comm 1 (h₁ + 1)) (s≤s z≤n)
... | .(h₁ + 1 + 1) , lrRotInit {h = h₁} n ln lrn t1 t2 t3 t4 , snd₁ = h₁ + 1 + 1 , (leftRightRotationInit n ln lrn t1 t2 t3 t4) ,′ snd₁ ,′ subst (λ x → 1 ≤ x) (+-comm 1 (h₁ + 1)) (s≤s z≤n)


test2 : Avl ℕ -∞ +∞ 2
test2 = node 5 (node 3 (empty -∞<n) (empty ([]<[] (s≤s (s≤s (s≤s (s≤s z≤n)))))) z≤n) 
               (empty n<+∞) (s≤s z≤n)

insertTest : Avl ℕ -∞ +∞ 2
insertTest = proj₁ (snd (insert 1 test2 -∞<n n<+∞))

insertTest2 : Avl ℕ -∞ +∞ 2
insertTest2 = proj₁ (snd (insert 4 test2 -∞<n n<+∞))

test3 : Avl ℕ -∞ +∞ 2
test3 = node 4 (node 1 (empty -∞<n) (empty ([]<[] (s≤s (s≤s z≤n)) )) z≤n)
               (node 5 (empty ([]<[] (s≤s (s≤s (s≤s (s≤s (s≤s z≤n))))) )) (empty n<+∞) z≤n) z≤n

insertTest3 : Avl ℕ -∞ +∞ 3
insertTest3 = proj₁ (snd (insert 2 test3 -∞<n n<+∞))

insertTest4 : Avl ℕ -∞ +∞ 3
insertTest4 = proj₁ (snd (insert 3 insertTest3 -∞<n n<+∞))

insertTest5 : Avl ℕ -∞ +∞ 3
insertTest5 = proj₁ (snd (insert 3 (proj₁ (snd (insert 0 insertTest3 -∞<n n<+∞))) -∞<n n<+∞))
-}

m≡sucn∧m≡1⇒n≡0 : ∀ {m n} → m ≡ suc n → m ≡ 1 → n ≡ 0
m≡sucn∧m≡1⇒n≡0 {m} {n} p1 p2 = cong pred (subst (λ x → x ≡ 1) p1 p2)

m≡o∧n≤o⇒m-n≤o : ∀ {m n o} → m ≡ o → n ≤ o → m - n ≤ o
m≡o∧n≤o⇒m-n≤o {m} {n} {o} p1 p2 rewrite p1 | m≤n⇒∣n-m∣≡n∸m p2 = m∸n≤m o n

simplifyLeftBound : {h x n : ℕ} {l : ℕ∞} → l <∞ [ x ] → Avl ℕ l [ n ] h → Avl ℕ ([ x ] ⊓∞ l) [ n ] h
simplifyLeftBound {h} {x} {n} {l} p t rewrite n<∞[]⇒[]⊓∞n≡n p = t

simplifyRightBound : {h x : ℕ} {u : ℕ∞} → [ x ] <∞ u → Avl ℕ [ x ] u h → Avl ℕ [ x ] ([ x ] ⊔∞ u) h
simplifyRightBound {h} {x} {l} p t rewrite []<∞n⇒[]⊔∞n≡n p = t

simplifybounds : {h x : ℕ} {l u : ℕ∞} → l <∞ [ x ] → [ x ] <∞ u → Avl ℕ l u h → Avl ℕ ([ x ] ⊓∞ l) ([ x ] ⊔∞ u) h
simplifybounds {h} {x} {l} {u} p1 p2 t rewrite n<∞[]⇒[]⊓∞n≡n p1 | []<∞n⇒[]⊔∞n≡n p2 = t

insert2 : {lower upper : ℕ∞} {h : ℕ} 
        → (x : ℕ) 
        → Avl ℕ lower upper h 
        → (p1 : lower <∞ [ x ]) 
        → (p2 : [ x ] <∞ upper) 
        → Σ[ h' ∈ ℕ ] 
            (Σ[ t ∈ Avl ℕ ([ x ] ⊓∞ lower) ([ x ] ⊔∞ upper) h' ] 
                ((h' ≡ h) 
                ⊎ 
                (Σ[ t ∈ Avl ℕ ([ x ] ⊓∞ lower) ([ x ] ⊔∞ upper) h' ]
                    ((Σ[ lower' ∈ ℕ∞ ] Σ[ upper' ∈ ℕ∞ ] Σ[ h'' ∈ ℕ ]
                        Σ[ t' ∈ Avl ℕ lower' upper' h'' ] 
                            (h' ≡ suc h × HeightIncTree3 t t'))
                    ⊎ (h' ≡ suc h × (HeightIncTreeInit t ⊎ HeightIncTreeInit2 t))))))
            × (0 < h')

insert'2 : {lower upper : ℕ∞} {h : ℕ} 
        → (x : ℕ) 
        → Avl ℕ lower upper h 
        → (p1 : lower <∞ [ x ]) 
        → (p2 : [ x ] <∞ upper) 
        → Σ[ h' ∈ ℕ ] 
            (InsertTree lower upper h') × 
                ((h' ≡ h) 
                ⊎ 
                (Σ[ t ∈ Avl ℕ ([ x ] ⊓∞ lower) ([ x ] ⊔∞ upper) h' ]
                    ((Σ[ lower' ∈ ℕ∞ ] Σ[ upper' ∈ ℕ∞ ] Σ[ h'' ∈ ℕ ]
                        Σ[ t' ∈ Avl ℕ lower' upper' h'' ] 
                            (h' ≡ suc h × HeightIncTree3 t t'))
                    ⊎ (h' ≡ suc h × (HeightIncTreeInit t ⊎ HeightIncTreeInit2 t)))))

insert'2 x (empty p) p1 p2 
    = 1 , avl x (empty p1) (empty p2) z≤n , inj₂ (node x (simplifyLeftBound p1 (empty p1)) (simplifyRightBound p2 (empty p2)) z≤n 
    , inj₂ (refl , inj₁ (basic-tree refl refl (simplifyLeftBound p1 (empty p1)) (simplifyRightBound p2 (empty p2)) z≤n refl)))
insert'2 x (node {l = l₁} {r = r₁} n l r p) p1 p2 with x <? n | x >? n --? n | x >? n
insert'2 x (node {l = l₁} {r = r₁} n l r p) p1 p2 | no ¬p | no ¬p₁ rewrite sym (x</n,x>/n⇒x≡n ¬p ¬p₁) = (l₁ ⊔ r₁) + 1 , avl {l = l₁} {r = r₁} x l r p , inj₁ refl
insert'2 x (node {l = l₁} {r = r₁} n l r p) p1 p2 | no ¬p | yes p₁ with newT
    where newT = insert2 x r ([]<[] p₁) p2 -- inserting in the right subtree
insert'2 {lower} {upper} x (node {l = l₁} {r = r₁} n l r p) p1 p2 | no ¬p | yes p₁ | fst₁ , (fst₂ , inj₁ x₁) , snd₁ rewrite m≥n⇒m⊓n≡n (<⇒≤ p₁) | []<∞n⇒[]⊔∞n≡n p2 | sym x₁ 
    = (l₁ ⊔ fst₁) + 1 , avl n l fst₂ p , inj₁ refl
insert'2 {lower} {upper} x (node {l = l₁} {r = r₁} n l r p) p1 p2 | no ¬p | yes p₁ | fst₁ , (fst₂ , inj₂ (fst₃ , inj₁ x₁)) , snd₁ = {!   !}
-- insert returns HeightIncTreeInit
insert'2 {lower} {upper} x (node {l = l₁} {r = r₁} n l r p) p1 p2 | no ¬p | yes p₁ | fst₁ , (fst₂ , inj₂ (fst₃ , inj₂ (fst₄ , inj₁ (basic-tree x₁ x₂ left₁ right₁ p₂ p3)))) , snd₁ with l₁ <? r₁ | l₁ >? r₁
insert'2 {lower} {upper} x (node {l = l₁} {r = r₁} n l r p) p1 p2 | no ¬p | yes p₁ | fst₁ , (fst₂ , inj₂ (fst₃ , inj₂ (fst₄ , inj₁ (basic-tree x₁ x₂ left₁ right₁ p₂ p3)))) , snd₁ | no ¬p₁ | no ¬p₂ 
    = l₁ ⊔ fst₁ + 1 , avl n l rightsubtreeInsert proofnew 
    , inj₂ (node n (subst (λ x → Avl ℕ x [ n ] l₁) (sym (n<∞[]⇒[]⊓∞n≡n p1)) l) {! rightsubtreeAvl fst₃ p₁  !} proofnew 
        , inj₂ ( heightchange , inj₂ (right-is-init l₁≡0 (subst (λ z → Avl ℕ z [ n ] l₁) (sym (n<∞[]⇒[]⊓∞n≡n p1)) l) {! rightsubtreeAvl fst₃ p₁  !} 
            (basic-tree x₁ x₂ (rightsubtreeAvl left₁ p₁) right₁ p₂ p3) proofnew refl) ))
    where rightsubtreeInsert : Avl ℕ [ n ] upper fst₁
          rightsubtreeInsert = subst (λ x → Avl ℕ [ x ] upper fst₁) (m≥n⇒m⊓n≡n (<⇒≤ p₁)) (subst (λ w → Avl ℕ [ x ⊓ n ] w fst₁) ([]<∞n⇒[]⊔∞n≡n p2) fst₃)
          fst₁≡1 : fst₁ ≡ 1
          fst₁≡1 rewrite sym p3 | x₁ | x₂ = refl
          proofnew : fst₁ - l₁ ≤ 1
          proofnew = m≡o∧n≤o⇒m-n≤o fst₁≡1 (subst (λ x → x - l₁ ≤ 1) (m≡sucn∧m≡1⇒n≡0 fst₄ fst₁≡1) p)
          rightsubtreeAvl : {x n fst₁ : ℕ} {upper : ℕ∞} → Avl ℕ [ x ⊓ n ] ([ x ] ⊔∞ upper) fst₁ → suc n ≤ x → Avl ℕ [ n ] ([ x ] ⊔∞ upper) fst₁
          rightsubtreeAvl {x} {n} {fst₁} {upper} t p₁ = subst (λ w → Avl ℕ [ w ] ([ x ] ⊔∞ upper) fst₁) (m≥n⇒m⊓n≡n (<⇒≤ p₁)) t
          r₁≡0 : r₁ ≡ 0
          r₁≡0 = subst (λ x → pred (suc r₁) ≡ pred x) fst₁≡1 (sym (cong pred fst₄))
          l₁≡0 : l₁ ≡ 0
          l₁≡0 = subst (λ x → pred (suc x) ≡ pred 1) (sym (x</n,x>/n⇒x≡n ¬p₁ ¬p₂)) (subst (λ x → pred (suc r₁) ≡ pred x) fst₁≡1 (sym (cong pred fst₄)))
          heightchange : l₁ ⊔ fst₁ + 1 ≡ suc (l₁ ⊔ r₁ + 1)
          heightchange rewrite fst₁≡1 | l₁≡0 | r₁≡0 = refl
insert'2 {lower} {upper} x (node {l = l₁} {r = r₁} n l r p) p1 p2 | no ¬p | yes p₁ | fst₁ , (fst₂ , inj₂ (fst₃ , inj₂ (fst₄ , inj₁ (basic-tree x₁ x₂ left₁ right₁ p₂ p3)))) , snd₁ | _ | yes p₃ 
    = l₁ ⊔ fst₁ + 1 , avl n l rightsubtreeInsert proofnew , inj₁ heightsame
    where rightsubtreeInsert : Avl ℕ [ n ] upper fst₁
          rightsubtreeInsert = subst (λ x → Avl ℕ [ x ] upper fst₁) (m≥n⇒m⊓n≡n (<⇒≤ p₁)) (subst (λ w → Avl ℕ [ x ⊓ n ] w fst₁) ([]<∞n⇒[]⊔∞n≡n p2) fst₃)
          fst₁≡1 : fst₁ ≡ 1
          fst₁≡1 rewrite sym p3 | x₁ | x₂ = refl
          proofnew : fst₁ - l₁ ≤ 1
          proofnew = m≡o∧n≤o⇒m-n≤o fst₁≡1 (subst (λ x → x - l₁ ≤ 1) (m≡sucn∧m≡1⇒n≡0 fst₄ fst₁≡1) p)
          r₁≡0 : r₁ ≡ 0
          r₁≡0 = subst (λ x → pred (suc r₁) ≡ pred x) fst₁≡1 (sym (cong pred fst₄))
          l₁≡1 : l₁ ≡ 1
          l₁≡1 = ≤-antisym (subst (λ x → x - l₁ ≤ 1) r₁≡0 p) (subst (λ x → suc x ≤ l₁) r₁≡0 p₃)
          heightsame : l₁ ⊔ fst₁ + 1 ≡ l₁ ⊔ r₁ + 1
          heightsame rewrite fst₁≡1 | l₁≡1 | r₁≡0 = refl
insert'2 {lower} {upper} x (node {l = l₁} {r = r₁} n l r p) p1 p2 | no ¬p | yes p₁ | fst₁ , (fst₂ , inj₂ (fst₃ , inj₂ (fst₄ , inj₁ (basic-tree x₁ x₂ left₁ right₁ p₂ p3)))) , snd₁ | yes p₃ | _ 
    = contradiction p₃ (subst (λ x → ¬ suc l₁ ≤ x) (sym r₁≡0) (<⇒≱ 0<1+n))
    where fst₁≡1 : fst₁ ≡ 1
          fst₁≡1 rewrite sym p3 | x₁ | x₂ = refl
          r₁≡0 : r₁ ≡ 0
          r₁≡0 = subst (λ x → pred (suc r₁) ≡ pred x) fst₁≡1 (sym (cong pred fst₄))
insert'2 {lower} {upper} x (node {l = l₁} {r = r₁} n l r p) p1 p2 | no ¬p | yes p₁ | fst₁ , (fst₂ , inj₂ (fst₃ , inj₂ (fst₄ , inj₂ y))) , snd₁ with fst₁ - l₁ ≤? 1 
insert'2 {lower} {upper} x (node {l = l₁} {r = r₁} n l r p) p1 p2 | no ¬p | yes p₁ | fst₁ , (fst₂ , inj₂ (fst₃ , inj₂ (fst₄ , inj₂ y))) , snd₁ | no ¬p₁ = {! y  !}
insert'2 {lower} {upper} x (node {l = l₁} {r = r₁} n l r p) p1 p2 | no ¬p | yes p₁ | fst₁ , (fst₂ , inj₂ (fst₃ , inj₂ (fst₄ , inj₂ y))) , snd₁ | yes p₂ with l₁ <? r₁ | l₁ >? r₁ 
insert'2 {lower} {upper} x (node {l = l₁} {r = r₁} n l r p) p1 p2 | no ¬p | yes p₁ | fst₁ , (fst₂ , inj₂ (.(subst (Avl ℕ [ x ⊓ n ] ([ x ] ⊔∞ upper)) p3 (node _ left₁ right₁ p₃)) , inj₂ (fst₄ , inj₂ (left-is-init p0 left₁ right₁ leftInit p₃ p3)))) , snd₁ | yes p₂ | no ¬p₁ | no ¬p₂ = {!   !}
insert'2 {lower} {upper} x (node {l = l₁} {r = r₁} n l r p) p1 p2 | no ¬p | yes p₁ | fst₁ , (fst₂ , inj₂ (fst₃ , inj₂ (fst₄ , inj₂ (right-is-init {l = l₂} {r = r₂} p0 left₁ right₁ (basic-tree x₁ x₂ left₂ right₂ p₄ p4) p₃ p3)))) , snd₁ | yes p₂ | no ¬p₁ | no ¬p₂ = {! p4  !} 
    {-= l₁ ⊔ fst₁ + 1 , avl n l rightsubtreeInsert p₂ 
        , inj₂ (node n (subst (λ x → Avl ℕ x [ n ] l₁) (sym (n<∞[]⇒[]⊓∞n≡n p1)) l) (rightsubtreeAvl fst₃ p₁) p₂ 
            , inj₁ ([ n ] , ([ x ] ⊔∞ upper) , fst₁ , rightsubtreeAvl fst₃ p₁ , heightchange 
                , right-subtree l₂≢/r₂ (rightsubtreeAvl left₁ p₁) right₁ p₃ p3 (simplifyLeftBound p1 l) (subst (λ x → x - l₁ ≤ 1) (sym p3) p₂) {!   !} {!   !} {!  refl !} ) )-} -- {! right-subtree ? ? ? ? ? ? ? ? ? ?  !})) (subst (λ x → l₁ ⊔ x + 1 ≡ l₁ ⊔ fst₁ + 1) (sym p3) refl)
    where rightsubtreeInsert : Avl ℕ [ n ] upper fst₁
          rightsubtreeInsert = subst (λ x → Avl ℕ [ x ] upper fst₁) (m≥n⇒m⊓n≡n (<⇒≤ p₁)) (subst (λ w → Avl ℕ [ x ⊓ n ] w fst₁) ([]<∞n⇒[]⊔∞n≡n p2) fst₃)
          rightsubtreeAvl : {x n fst₁ : ℕ} {upper : ℕ∞} → Avl ℕ [ x ⊓ n ] ([ x ] ⊔∞ upper) fst₁ → suc n ≤ x → Avl ℕ [ n ] ([ x ] ⊔∞ upper) fst₁
          rightsubtreeAvl {x} {n} {fst₁} {upper} fst₂ p₁ = subst (λ w → Avl ℕ [ w ] ([ x ] ⊔∞ upper) fst₁) (m≥n⇒m⊓n≡n (<⇒≤ p₁)) fst₂
          l₁≡r₁ : l₁ ≡ r₁
          l₁≡r₁ rewrite x</n,x>/n⇒x≡n ¬p₁ ¬p₂ = refl
          heightchange : l₁ ⊔ fst₁ + 1 ≡ suc (l₁ ⊔ r₁ + 1)
          heightchange rewrite l₁≡r₁ | fst₄ | ⊔-idem r₁ | m≤n⇒m⊔n≡n (n≤1+n r₁) = refl
          r₂≡1 : r₂ ≡ 1
          r₂≡1 rewrite sym p4 | x₁ | x₂ = refl
          l₂≢/r₂ : l₂ ≢ r₂
          l₂≢/r₂ rewrite p0 | r₂≡1 = λ ()
          lower<∞n : lower <∞ [ n ]
          lower<∞n = {!   !}
insert'2 {lower} {upper} x (node {l = l₁} {r = r₁} n l r p) p1 p2 | no ¬p | yes p₁ | fst₁ , (fst₂ , inj₂ (fst₃ , inj₂ (fst₄ , inj₂ y))) , snd₁ | yes p₂ | _ | yes p₃ = {!   !}
insert'2 {lower} {upper} x (node {l = l₁} {r = r₁} n l r p) p1 p2 | no ¬p | yes p₁ | fst₁ , (fst₂ , inj₂ (fst₃ , inj₂ (fst₄ , inj₂ y))) , snd₁ | yes p₂ | yes p₃ | _ = {!   !}
insert'2 x (node {l = l₁} {r = r₁} n l r p) p1 p2 | yes p₁ | _ = {!   !}


insert2 {lower} {upper} {h} x t p1 p2 with insert'2 x t p1 p2 
... | .((l₁ ⊔ r₁) + 1) , avl {l = l₁} {r = r₁} n l r p , snd₁ = l₁ ⊔ r₁ + 1 , (simplifybounds p1 p2 (node n l r p) , snd₁) , subst (λ x → 1 ≤ x) (+-comm 1 (l₁ ⊔ r₁)) (s≤s z≤n)
... | .(h₁ + 1 + 1) , llRot {h = h₁} n ln t1 t2 t3 , snd₁ = h₁ + 1 + 1 , (simplifybounds p1 p2 (leftRotation1 n ln t1 t2 t3) , snd₁) , subst (λ x → 1 ≤ x) (+-comm 1 (h₁ + 1)) (s≤s z≤n)
... | .(h₁ + 1 + 1) , rrRot {h = h₁} n rn t1 t2 t3 , snd₁ = h₁ + 1 + 1 , (simplifybounds p1 p2 (rightRotation1 n rn t1 t2 t3) , snd₁) , subst (λ x → 1 ≤ x) (+-comm 1 (h₁ + 1)) (s≤s z≤n)
... | .(h₁ + 1 + 1 + 1) , lrRotL {h = h₁} n ln lrn t1 t2 t3 t4 , snd₁ = h₁ + 1 + 1 + 1 , (simplifybounds p1 p2 (leftRightRotationL n ln lrn t1 t2 t3 t4) , snd₁) , subst (λ x → 1 ≤ x) (+-comm 1 (h₁ + 1 + 1)) (s≤s z≤n)
... | .(h₁ + 1 + 1 + 1) , lrRotR {h = h₁} n ln lrn t1 t2 t3 t4 , snd₁ = h₁ + 1 + 1 + 1 , (simplifybounds p1 p2 (leftRightRotationR n ln lrn t1 t2 t3 t4) , snd₁) , subst (λ x → 1 ≤ x) (+-comm 1 (h₁ + 1 + 1)) (s≤s z≤n)
... | .(h₁ + 1 + 1 + 1) , rlRotL {h = h₁} n rn rln t1 t2 t3 t4 , snd₁ = h₁ + 1 + 1 + 1 , (simplifybounds p1 p2 (rightLeftRotationL n rn rln t1 t2 t3 t4) , snd₁) , subst (λ x → 1 ≤ x) (+-comm 1 (h₁ + 1 + 1)) (s≤s z≤n)
... | .(h₁ + 1 + 1 + 1) , rlRotR {h = h₁} n rn rln t1 t2 t3 t4 , snd₁ = h₁ + 1 + 1 + 1 , (simplifybounds p1 p2 (rightLeftRotationR n rn rln t1 t2 t3 t4) , snd₁) , subst (λ x → 1 ≤ x) (+-comm 1 (h₁ + 1 + 1)) (s≤s z≤n)
... | .(h₁ + 1 + 1) , rlRotInit {h = h₁} n rn rln t1 t2 t3 t4 , snd₁ = h₁ + 1 + 1 , (simplifybounds p1 p2 (rightLeftRotationInit n rn rln t1 t2 t3 t4) , snd₁) , subst (λ x → 1 ≤ x) (+-comm 1 (h₁ + 1)) (s≤s z≤n)
... | .(h₁ + 1 + 1) , lrRotInit {h = h₁} n ln lrn t1 t2 t3 t4 , snd₁ = h₁ + 1 + 1 , (simplifybounds p1 p2 (leftRightRotationInit n ln lrn t1 t2 t3 t4) , snd₁) , subst (λ x → 1 ≤ x) (+-comm 1 (h₁ + 1)) (s≤s z≤n)




                    