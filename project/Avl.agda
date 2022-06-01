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

proof23,0 : ∀ {m n o p} → n ≡ suc m → p - o ≤ 1 → m ⊔ n + 1 ≡ suc p → suc m ≤ n → m -ᴺ o ≡ 0
proof23,0 {m} {n} {o} {p} p1 p2 p3 p4 = ≤-antisym (≤-pred {!   !}) {!   !}

proof23 : ∀ {m n o p} → n ≡ suc m → p - o ≤ 1 → m ⊔ n + 1 ≡ suc p → suc m ≤ n → m ≡ o
proof23 {m} {n} {o} {p} p1 p2 p3 p4 = ≤-antisym (m∸n≡0⇒m≤n {!   !}) (m∸n≡0⇒m≤n {!   !})

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

proof27,1 : ∀ {m n o} → n ≡ suc m → m ≡ o → n ≡ o + 1
proof27,1 {m} {n} {o} p1 p2 rewrite +-comm o 1 | sym p2 = p1


insert : {lower upper : ℕ∞} {h : ℕ} → (x : ℕ) → Avl ℕ lower upper h → (p1 : lower <∞ [ x ]) → (p2 : [ x ] <∞ upper) → Σ[ h' ∈ ℕ ] ((Avl ℕ ([ x ] ⊓∞ lower) ([ x ] ⊔∞ upper) h') × ((h' ≡ h) ⊎ (h' ≡ suc h)) × (0 < h'))

insert' : {lower upper : ℕ∞} {h : ℕ} → (x : ℕ) → Avl ℕ lower upper h → (p1 : lower <∞ [ x ]) → (p2 : [ x ] <∞ upper) → Σ[ h' ∈ ℕ ] ((InsertTree lower upper h') × ((h' ≡ h) ⊎ (h' ≡ suc h)))
insert' x (empty p) p1 p2 = 1 , (avl x (empty p1) (empty p2) z≤n) ,′ inj₂ refl
insert' x (node {l = l₁} {r = r₁} n l r p) p1 p2 with x <? n | x >? n --? n | x >? n
insert' x (node {l = l₁} {r = r₁} n l r p) p1 p2 | no ¬p | no ¬p₁ rewrite sym (x</n,x>/n⇒x≡n ¬p ¬p₁) = suc (l₁ ⊔ r₁) , (avl {l = l₁} {r = r₁} x l r p) ,′ inj₁ (+-comm 1 (l₁ ⊔ r₁))
insert' x (node {l = l₁} {r = r₁} n l r p) p1 p2 | no ¬p | yes p₁ with newT
    where newT = insert x r ([]<[] p₁) p2
insert' x (node {l = l₁} {r = r₁} n l r p) p1 p2 | no ¬p | yes p₁ | fst₁ , fst₂ , inj₁ x₁ , snd₁ rewrite m≥n⇒m⊓n≡n (<⇒≤ p₁) | []<∞n⇒[]⊔∞n≡n p2 | sym x₁ = suc (l₁ ⊔ fst₁) , (avl n l fst₂ p) ,′ inj₁ (+-comm 1 (l₁ ⊔ fst₁))
insert' x (node {l = l₁} {r = r₁} n l r p) p1 p2 | no ¬p | yes p₁ | fst₁ , fst₂ , inj₂ y , snd₁ with fst₁ - l₁ ≤? 1 --? 1
insert' x (node {l = l₁} {r = r₁} n l r p) p1 p2 | no ¬p | yes p₁ | .(d1 ⊔ d2 + 1) , node {l = d1} {r = d2} n₁ fst₂ fst₃ x₁ , inj₂ y , snd₁ | no ¬p₁ with d2 >? d1
insert' x (node {l = l₁} {r = r₁} n l r p) p1 p2 | no ¬p | yes p₁ | .(d1 ⊔ d2 + _) , node {l = d1} {r = d2} n₁ fst₂ fst₃ x₁ , inj₂ y , snd₁ | no ¬p₁ | false because proof₁ = {!   !}
insert' x (node {l = l₁} {r = r₁} n l r p) p1 p2 | no ¬p | yes p₁ | .(d1 ⊔ d2 + 1) , node {l = d1} {r = d2} n₁ fst₂ fst₃ x₁ , inj₂ y , snd₁ | no ¬p₁ | yes p₂ rewrite m≥n⇒m⊓n≡n (<⇒≤ p₁) | []<∞n⇒[]⊔∞n≡n p2 | proof27 (proof22 x₁ p₂) p y p₂ ¬p₁ | proof27,1 (proof22 x₁ p₂) (proof27 (proof22 x₁ p₂) p y p₂ ¬p₁) 
    = l₁ + 1 + 1 , (rrRot n n₁ l fst₂ fst₃) ,′ inj₁ (cong (λ x → x + 1) (subst (λ x → l₁ + 1 ≡ x) (sym (m≤n⇒m⊔n≡n (subst (λ x → l₁ ≤ x) (subst (λ x → x ≡ r₁) (m≤n⇒m⊔n≡n (<⇒≤ p₂)) (proof4,0 y)) (subst (λ x → l₁ ≤ x) (sym (proof27,1 (proof22 x₁ p₂) (proof27 (proof22 x₁ p₂) p y p₂ ¬p₁))) (subst (λ x → l₁ ≤ x) (+-comm 1 l₁) (n≤1+n l₁)))))) (subst (λ x → l₁ + 1 ≡ x) p4 {! p3  !}))) --inj₂ (subst (λ x → x ≡ suc (l₁ ⊔ r₁ + 1)) (sym (+-comm (l₁ + 1) 1)) (cong suc (cong (λ x → x + 1) (sym (m≥n⇒m⊔n≡m {!   !})))))
    where p3 : d1 ≡ l₁
          p3 = proof27 (proof22 x₁ p₂) p y p₂ ¬p₁
          p4 : d2 ≡ r₁
          p4 = subst (λ x → x ≡ r₁) (m≤n⇒m⊔n≡n (<⇒≤ p₂)) (proof4,0 y)
          p5 : d2 ≡ suc l₁
          p5 = {! subst (λ x → l₁ ≤ x) (sym (proof27,1 (proof22 x₁ p₂) (proof27 (proof22 x₁ p₂) p y p₂ ¬p₁))) (subst (λ x → l₁ ≤ x) (+-comm 1 l₁) (n≤1+n l₁))  !}
insert' x (node {l = l₁} {r = r₁} n l r p) p1 p2 | no ¬p | yes p₁ | fst₁ , fst₂ , inj₂ y , snd₁ | yes p₂ rewrite m≥n⇒m⊓n≡n (<⇒≤ p₁) | []<∞n⇒[]⊔∞n≡n p2 with l₁ <? r₁ | l₁ >? r₁ --? r₁ | l₁ >? r₁
insert' x (node {l = l₁} {r = r₁} n l r p) p1 p2 | no ¬p | yes p₁ | fst₁ , fst₂ , inj₂ y , snd₁ | yes p₂ | no ¬p₁ | no ¬p₂ rewrite sym (x</n,x>/n⇒x≡n ¬p₁ ¬p₂) | ⊔-idem l₁ = suc (l₁ ⊔ fst₁) , (avl n l fst₂ p₂) ,′ inj₂ (cong suc (subst (λ x → l₁ ⊔ x ≡ l₁ + 1) (sym y) (subst (λ x → x ≡ l₁ + 1) (sym (m≤n⇒m⊔n≡n (n≤1+n l₁))) (+-comm 1 l₁)))) 
insert' x (node {l = l₁} {r = r₁} n l r p) p1 p2 | no ¬p | yes p₁ | fst₁ , fst₂ , inj₂ y , snd₁ | yes p₂ | no ¬p₁ | yes p₃ rewrite m≥n⇒m⊔n≡m (<⇒≤ p₃) | +-comm l₁ 1 = suc (l₁ ⊔ fst₁) , (avl n l fst₂ p₂) ,′ inj₁ (cong suc (m≥n⇒m⊔n≡m (subst (λ x → l₁ ≥ x) (sym y) p₃)))
insert' x (node {l = l₁} {r = r₁} n l r p) p1 p2 | no ¬p | yes p₁ | fst₁ , fst₂ , inj₂ y , snd₁ | yes p₂ | yes p₃ | rez2 rewrite m≤n⇒m⊔n≡n (<⇒≤ p₃) = suc (l₁ ⊔ fst₁) , (avl n l fst₂ p₂) ,′ inj₂ (cong suc (proof24 y p₃))
insert' x (node {l = l₁} {r = r₁} n l r p) p1 p2 | yes p₁ | rez2 = {!   !}



insert {lower} {upper} {h} x t p1 p2 rewrite n<∞[]⇒[]⊓∞n≡n p1 | []<∞n⇒[]⊔∞n≡n p2 with insert' x t p1 p2
... | .(suc (l₁ ⊔ r₁)) , avl {l = l₁} {r = r₁} n l r p , snd₁ = (l₁ ⊔ r₁ + 1) , (node n l r p) ,′ subst (λ x → x ≡ h ⊎ x ≡ suc h) (+-comm 1 (l₁ ⊔ r₁)) snd₁ ,′ subst (λ x → 1 ≤ x) (+-comm 1 (l₁ ⊔ r₁)) (s≤s z≤n)
... | .(h₁ + 1 + 1) , llRot {h = h₁} n ln t1 t2 t3 , snd₁ = h₁ + 1 + 1 , (leftRotation1 n ln t1 t2 t3) ,′ snd₁ ,′ subst (λ x → 1 ≤ x) (+-comm 1 (h₁ + 1)) (s≤s z≤n)
... | .(h₁ + 1 + 1) , rrRot {h = h₁} n rn t1 t2 t3 , snd₁ = h₁ + 1 + 1 , (rightRotation1 n rn t1 t2 t3) ,′ snd₁ ,′ subst (λ x → 1 ≤ x) (+-comm 1 (h₁ + 1)) (s≤s z≤n)
... | .(h₁ + 1 + 1 + 1) , lrRotL {h = h₁} n ln lrn t1 t2 t3 t4 , snd₁ = h₁ + 1 + 1 + 1 , (leftRightRotationL n ln lrn t1 t2 t3 t4) ,′ snd₁ ,′ subst (λ x → 1 ≤ x) (+-comm 1 (h₁ + 1 + 1)) (s≤s z≤n)
... | .(h₁ + 1 + 1 + 1) , lrRotR {h = h₁} n ln lrn t1 t2 t3 t4 , snd₁ = h₁ + 1 + 1 + 1 , (leftRightRotationR n ln lrn t1 t2 t3 t4) ,′ snd₁ ,′ subst (λ x → 1 ≤ x) (+-comm 1 (h₁ + 1 + 1)) (s≤s z≤n)
... | .(h₁ + 1 + 1 + 1) , rlRotL {h = h₁} n rn rln t1 t2 t3 t4 , snd₁ = h₁ + 1 + 1 + 1 , (rightLeftRotationL n rn rln t1 t2 t3 t4) ,′ snd₁ ,′ subst (λ x → 1 ≤ x) (+-comm 1 (h₁ + 1 + 1)) (s≤s z≤n)
... | .(h₁ + 1 + 1 + 1) , rlRotR {h = h₁} n rn rln t1 t2 t3 t4 , snd₁ = h₁ + 1 + 1 + 1 , (rightLeftRotationR n rn rln t1 t2 t3 t4) ,′ snd₁ ,′ subst (λ x → 1 ≤ x) (+-comm 1 (h₁ + 1 + 1)) (s≤s z≤n)

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



               