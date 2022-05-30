{-# OPTIONS --allow-unsolved-metas #-}
module Proofs where

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
open import Datatypes

<∞-trans : {n m k : ℕ∞} → n <∞ m → m <∞ k → n <∞ k
<∞-trans -∞<n      q         = -∞<n
<∞-trans ([]<[] p) ([]<[] q) = []<[] (≤-trans p (<⇒≤ q))
<∞-trans ([]<[] p) n<+∞      = n<+∞
<∞-trans n<+∞      n<+∞      = n<+∞

lower<∞upper : {h : ℕ} {lower upper : ℕ∞} (t : Avl ℕ lower upper h) → lower <∞ upper
lower<∞upper {.zero} {lower} {upper} (empty p) = p
lower<∞upper {.(l₁ ⊔ r₁ + 1)} {lower} {upper} (node {l = l₁} {r = r₁} n l r x) = <∞-trans (lower<∞upper l) (lower<∞upper r) 

x∈t⇒l<x : {x h : ℕ} {lower upper : ℕ∞} {t : Avl ℕ lower upper h} → x ∈ t → lower <∞ [ x ]
x∈t⇒l<x {x} {h} {lower} {upper} {node x l r p} here = lower<∞upper l
x∈t⇒l<x (left p1) = x∈t⇒l<x p1
x∈t⇒l<x {x} {h} {lower} {upper} {node x₁ l r p} (right p1) = <∞-trans (lower<∞upper l) (x∈t⇒l<x p1)

x∈t⇒x<u : {x h : ℕ} {lower upper : ℕ∞} {t : Avl ℕ lower upper h} → x ∈ t → [ x ] <∞ upper
x∈t⇒x<u {x} {h} {lower} {upper} {node x l r p} here = lower<∞upper r
x∈t⇒x<u {x} {h} {lower} {upper} {node x₁ l r p} (left p1) = <∞-trans (x∈t⇒x<u p1) (lower<∞upper r)
x∈t⇒x<u (right p) = x∈t⇒x<u p

[]<[]⇒< : ∀ {m n} → [ m ] <∞ [ n ] → m < n
[]<[]⇒< {m} {n} ([]<[] x) = x

<⇒[]<[] : ∀ {m n} → m < n → [ m ] <∞ [ n ]
<⇒[]<[] {m} {n} p = []<[] p


notinl⇒notint : {x n hl hr : ℕ} {lower upper : ℕ∞} {l : Avl ℕ lower [ n ] hl} {r : Avl ℕ [ n ] upper hr} {p : (hr - hl) ≤ 1} → x < n → ¬ (x ∈ l) → ¬ (x ∈ (node n l r p))
notinl⇒notint p1 p2 here = <-irrefl refl p1
notinl⇒notint p1 p2 (left p) = p2 p
notinl⇒notint p1 p2 (right p) = <-asym p1 ([]<[]⇒< (x∈t⇒l<x p))

notinr⇒notint : {x n hl hr : ℕ} {lower upper : ℕ∞} {l : Avl ℕ lower [ n ] hl} {r : Avl ℕ [ n ] upper hr} {p : (hr - hl) ≤ 1} → x > n → ¬ (x ∈ r) → ¬ (x ∈ (node n l r p))
notinr⇒notint p1 p2 here = <-irrefl refl p1
notinr⇒notint p1 p2 (left p) = <-asym p1 ([]<[]⇒< (x∈t⇒x<u p))
notinr⇒notint p1 p2 (right p) = p2 p

x∈l⇒x∈t : {x n hl hr : ℕ} {lower upper : ℕ∞} {l : Avl ℕ lower [ n ] hl} {r : Avl ℕ [ n ] upper hr} {p : (hr - hl) ≤ 1} → x < n → (x ∈ l) ⊎ ¬ (x ∈ l) → (x ∈ node n l r p) ⊎ ¬ (x ∈ node n l r p)
x∈l⇒x∈t p1 p2 = Data.Sum.Base.map left (notinl⇒notint p1) p2

x∈r⇒x∈t : {x n hl hr : ℕ} {lower upper : ℕ∞} {l : Avl ℕ lower [ n ] hl} {r : Avl ℕ [ n ] upper hr} {p : (hr - hl) ≤ 1} → x > n → (x ∈ r) ⊎ ¬ (x ∈ r) → (x ∈ node n l r p) ⊎ ¬ (x ∈ node n l r p)
x∈r⇒x∈t p1 p2 = Data.Sum.Base.map right (notinr⇒notint p1) p2


x</n,x>/n⇒x≡n : ∀ {x n : ℕ} → ¬ x < n → ¬ n < x → x ≡ n
x</n,x>/n⇒x≡n p1 p2 = ≤∧≮⇒≡ (≮⇒≥ p2) p1

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
proof4,0 {m} {n} p rewrite +-comm m 1 = suc-injective p

proof4 : ∀ {m n o} → m ≤ n → m ⊔ n + 1 ≡ suc (suc o) → n ≡ suc o
proof4 {m} {n} {o} p q = (begin
                          n ≡⟨ sym (m≤n⇒m⊔n≡n p) ⟩
                          m ⊔ n ≡⟨ proof4,0 q ⟩ --cong {!  !} {!   !} ⟩
                          suc o
                          ∎)

proof5 : ∀ {m n o} → m ≡ suc n → m ≡ suc o → n ≡ o
proof5 {m} {n} {o} p1 p2 = suc-injective (trans (sym p1) p2)

proof6 : ∀ {m n o} → o + 1 ≡ suc(suc m) → o ≡ suc n → m ⊔ n + 1 ⊔ o ≡ o
proof6 {m} {n} {o} p1 p2 = (begin
                            m ⊔ n + 1 ⊔ o ≡⟨ cong (λ x → x + 1 ⊔ o) (m≤n⇒m⊔n≡n (≤-reflexive ((proof5 (proof4,0 p1) p2)))) ⟩
                            n + 1 ⊔ o ≡⟨ cong (λ x → x ⊔ o) (+-comm n 1) ⟩
                            suc n ⊔ o ≡⟨ cong (λ x → x ⊔ o) (sym p2) ⟩
                            o ⊔ o ≡⟨ m≤n⇒m⊔n≡n (≤-reflexive refl) ⟩
                            o
                            ∎)

proof6,01 : ∀ {m n o} → o + 1 ≡ suc(suc m) → o ≡ suc n → n ⊔ m + 1 ⊔ o ≡ o
proof6,01 {m} {n} {o} p1 p2 = (begin
                            n ⊔ m + 1 ⊔ o ≡⟨ cong (λ x → x + 1 ⊔ o) (m≥n⇒m⊔n≡m (≤-reflexive ((proof5 (proof4,0 p1) p2)))) ⟩
                            n + 1 ⊔ o ≡⟨ cong (λ x → x ⊔ o) (+-comm n 1) ⟩
                            suc n ⊔ o ≡⟨ cong (λ x → x ⊔ o) (sym p2) ⟩
                            o ⊔ o ≡⟨ m≤n⇒m⊔n≡n (≤-reflexive refl) ⟩
                            o
                            ∎)

proof6,1 : ∀ {m n o} → o + 1 ≡ suc(suc m) → o ≡ suc n → o ⊔ (m ⊔ n + 1) ≡ o
proof6,1 {m} {n} {o} p1 p2 rewrite ⊔-comm o (m ⊔ n + 1) = proof6 p1 p2

proof6,2 : ∀ {m n o} → o + 1 ≡ suc(suc m) → o ≡ suc n → o ⊔ (n ⊔ m + 1) ≡ o
proof6,2 {m} {n} {o} p1 p2 rewrite ⊔-comm o (n ⊔ m + 1) = proof6,01 p1 p2

proof7,0 : (m : ℕ) → m - m ≡ 0
proof7,0 (zero) = refl
proof7,0 (suc m) = proof7,0 m

proof7 : ∀ {m n} → m ≡ n → m - n ≡ 0
proof7 {zero} {n} p = sym p
proof7 {suc m} {n} p = (begin 
                        suc m - n ≡⟨ cong (λ x → suc m - x) (sym p) ⟩
                        m - m ≡⟨ proof7,0 m ⟩
                        0
                        ∎)

proof8 : ∀ {m n o} → m + 1 ≡ suc (suc n) → m ≡ suc o → n - o ≤ 1
proof8 {m} {n} {o} p1 p2 = ≤-step (≤-reflexive (proof7 (proof5 (proof4,0 p1) p2)))

proof8,1 : ∀ {m n o} → m + 1 ≡ suc (suc n) → m ≡ suc o → o - n ≤ 1
proof8,1 {m} {n} {o} p1 p2 = ≤-step (≤-reflexive (proof7 (proof5 p2 (proof4,0 p1))))


proof10,0 : ∀ {m n o} → m + 1 ≡ suc (suc n) → m ≡ suc o → ((o ⊔ n) + 1) ≡ m
proof10,0 {m} {n} {o} p1 p2 = (begin
                              ((o ⊔ n) + 1) ≡⟨ cong (λ x → x + 1) (m≥n⇒m⊔n≡m (≤-reflexive (proof5 (proof4,0 p1) p2))) ⟩ 
                              o + 1 ≡⟨ sym (trans p2 (+-comm 1 o)) ⟩
                              m
                              ∎)

proof10 : ∀ {m n o} → m + 1 ≡ suc (suc n) → m ≡ suc o → ((o ⊔ n) + 1) - m ≤ 1
proof10 {m} {n} {o} p1 p2 = ≤-step (≤-reflexive (proof7 (proof10,0 p1 p2)))

proof10,10 : ∀ {m n o} → m + 1 ≡ suc (suc n) → m ≡ suc o → ((n ⊔ o) + 1) ≡ m
proof10,10 {m} {n} {o} p1 p2 = (begin
                              ((n ⊔ o) + 1) ≡⟨ cong (λ x → x + 1) (m≤n⇒m⊔n≡n (≤-reflexive (proof5 (proof4,0 p1) p2))) ⟩ 
                              o + 1 ≡⟨ sym (trans p2 (+-comm 1 o)) ⟩
                              m
                              ∎)

proof10,1 : ∀ {m n o} → m + 1 ≡ suc (suc n) → m ≡ suc o → ((n ⊔ o) + 1) - m ≤ 1
proof10,1 {m} {n} {o} p1 p2 = ≤-step (≤-reflexive (proof7 (proof10,10 p1 p2)))

proof10,2 : ∀ {m n o} → m + 1 ≡ suc (suc n) → m ≡ suc o → m - ((n ⊔ o) + 1) ≤ 1
proof10,2 {m} {n} {o} p1 p2 = ≤-step (≤-reflexive (proof7 (sym (proof10,10 p1 p2))))

proof11 : ∀ {m n o} → n ⊔ o + 1 + 1 ≡ suc (suc m) → (o - n) ≤ 1 → (m - o) ≤ 1
proof11 {m} {n} {o} p1 p2 with ⊔-sel n o
... | inj₁ x rewrite sym (proof4,0 (proof4,0 p1)) | x | ∣-∣-comm o n = p2
... | inj₂ y rewrite sym (proof4,0 (proof4,0 p1)) | y | ∣n-n∣≡0 o = z≤n

proof12 : ∀ {m n} → (m + 1) ⊔ (n + 1) ≡ (m ⊔ n) + 1
proof12 {m} {n} rewrite +-comm m 1 | +-comm n 1 | +-comm (m ⊔ n) 1 = refl

proof13,1 : ∀ {p n} → p ⊔ n ⊔ n ⊔ (p ⊔ (p ⊔ n)) ≡ p ⊔ n
proof13,1 {p} {n} = (begin
                    ((p ⊔ n) ⊔ n) ⊔ (p ⊔ (p ⊔ n)) ≡⟨ cong (λ x → x ⊔ (p ⊔ (p ⊔ n))) (⊔-assoc p n n) ⟩
                    p ⊔ (n ⊔ n) ⊔ (p ⊔ (p ⊔ n)) ≡⟨ cong (λ x → p ⊔ x ⊔ (p ⊔ (p ⊔ n))) (⊔-idem n) ⟩
                    p ⊔ n ⊔ (p ⊔ (p ⊔ n)) ≡⟨ cong (λ x → p ⊔ n ⊔ x) (sym (⊔-assoc p p n)) ⟩
                    p ⊔ n ⊔ (p ⊔ p ⊔ n) ≡⟨ cong (λ x → p ⊔ n ⊔ x) (cong (λ x → x ⊔ n) (⊔-idem p)) ⟩
                    p ⊔ n ⊔ (p ⊔ n) ≡⟨ ⊔-idem (p ⊔ n) ⟩
                    p ⊔ n
                    ∎)

proof13 : ∀ {m n o p} → n ⊔ p + 1 ≡ suc m → n ⊔ p + 1 + 1 ≡ suc (suc o) → m ⊔ n + 1 ⊔ (p ⊔ o + 1) ≡ n ⊔ p + 1
proof13 {m} {n} {o} {p} p1 p2 rewrite proof12 {m ⊔ n} {p ⊔ o} | sym (proof4,0 p1) | ⊔-comm n p | sym (proof4,0 (proof4,0 p2)) 
    = cong (λ x → x + 1) (proof13,1 {p} {n})

proof14 : ∀ {h} → h ⊔ h + 1 ⊔ h ≡ h + 1
proof14 {h} rewrite ⊔-idem h = m≥n⇒m⊔n≡m (subst (λ x → x ≥ h) (+-comm 1 h) (<⇒≤ (n<1+n h)))

proof15 : ∀ {h} → h - h ≤ 1
proof15 {h} rewrite ∣n-n∣≡0 h = z≤n

proof16,0 : ∀ {h} → h ≤ h + 1
proof16,0 {h} rewrite +-comm h 1 = <⇒≤ (n<1+n h)

proof16,01 : ∀ {h} → (h + 1) - h ≤ 1
proof16,01 {h} rewrite m≤n⇒∣n-m∣≡n∸m (proof16,0 {h}) | +-∸-comm {h} 1 {h} (≤-refl {h}) | n∸n≡0 h = s≤s z≤n

proof16,02 : ∀ {h} → h - (h + 1) ≤ 1
proof16,02 {h} rewrite ∣-∣-comm h (h + 1) = proof16,01 {h}

proof16 : ∀ {h} → h - (h ⊔ h + 1) ≤ 1
proof16 {h} rewrite ⊔-idem h | ∣-∣-comm h (h + 1) = proof16,01 {h}

proof16,1 : ∀ {h} → (h + 1) - (h ⊔ h + 1) ≤ 1
proof16,1 {h} rewrite ⊔-idem h | ∣n-n∣≡0 (h + 1) = z≤n

proof16,2 : ∀ {h} → (h ⊔ h + 1) - (h + 1) ≤ 1
proof16,2 {h} rewrite ∣-∣-comm (h ⊔ h + 1) (h + 1) = proof16,1 {h}

proof17 : ∀ {h} → h ⊔ h + 1 ⊔ (h + 1) + 1 ≡ h + 1 + 1
proof17 {h} rewrite ⊔-idem h | ⊔-idem (h + 1) = refl

proof17,1 : ∀ {h} → h + 1 ⊔ (h ⊔ h + 1) + 1 ≡ h + 1 + 1
proof17,1 {h} rewrite ⊔-comm (h + 1) (h ⊔ h + 1) = proof17 {h}

proof18,0 : ∀ {h} → h ⊔ (h + 1) ≡ h + 1
proof18,0 {h} rewrite m≤n⇒m⊔n≡n (proof16,0 {h})  = refl

proof18 : ∀ {h} → h + 1 ⊔ (h + 1) + 1 ⊔ (h ⊔ (h + 1) + 1) + 1 ≡ h + 1 + 1 + 1
proof18 {h} rewrite ⊔-idem (h + 1) | proof18,0 {h} | ⊔-idem (h + 1 + 1) = cong (λ x → x + 1) refl

proof18,1 : ∀ {h} → h + 1 ⊔ h + 1 ⊔ (h + 1 ⊔ (h + 1) + 1) + 1 ≡ h + 1 + 1 + 1
proof18,1 {h} rewrite ⊔-comm (h + 1) h | ⊔-comm (h ⊔ (h + 1) + 1) (h + 1 ⊔ (h + 1) + 1)  = proof18 {h}

proof19 : ∀ {h} → ((h ⊔ (h + 1) + 1) - (h + 1 ⊔ (h + 1) + 1)) ≤ 1
proof19 {h} rewrite ⊔-idem (h + 1) | proof18,0 {h} = proof15 {h + 1 + 1}

proof19,1 : ∀ {h} → (h + 1 ⊔ (h + 1) + 1) - (h + 1 ⊔ h + 1) ≤ 1
proof19,1 {h} rewrite ⊔-comm (h + 1) h | ∣-∣-comm (h + 1 ⊔ (h + 1) + 1) (h ⊔ (h + 1) + 1) = proof19 {h}

proof9,0rev : ∀ {m n} → m < n → [ m ] <∞ [ n ]
proof9,0rev {m} {n} p = []<[] p

proof9 : ∀ {m n} → m <∞ n → (n ⊓∞ m) <∞ n
proof9 { -∞} { -∞} p = p
proof9 { -∞} {[ x ]} p = p
proof9 { -∞} {+∞} p = p
proof9 {[ x ]} {[ y ]} p rewrite ⊓-comm y x | m≤n⇒m⊓n≡m (<⇒≤ ([]<[]⇒< p)) = p
proof9 {[ x ]} {+∞} p = p
proof9 {+∞} {+∞} p = p

[]<∞n⇒[]⊔∞n≡n : ∀ {m n} → [ m ] <∞ n → [ m ] ⊔∞ n ≡ n
[]<∞n⇒[]⊔∞n≡n {m} {[ x ]} p rewrite m≤n⇒m⊔n≡n (<⇒≤ ([]<[]⇒< p)) = refl
[]<∞n⇒[]⊔∞n≡n {m} {+∞} p = refl

[]<∞n⇒[]<∞[]⊔∞n : ∀ {m n} → [ m ] <∞ n → [ m ] <∞ ([ m ] ⊔∞ n)
[]<∞n⇒[]<∞[]⊔∞n {m} {n} p rewrite []<∞n⇒[]⊔∞n≡n p = p

n<∞[]⇒[]⊓∞n≡n : ∀ {m n} → n <∞ [ m ] → [ m ] ⊓∞ n ≡ n
n<∞[]⇒[]⊓∞n≡n {m} { -∞} p = refl
n<∞[]⇒[]⊓∞n≡n {m} {[ x ]} p rewrite m≥n⇒m⊓n≡n (<⇒≤ ([]<[]⇒< p)) = refl

⊓∞-sym : ∀ {m n} → m ⊓∞ n ≡ n ⊓∞ m
⊓∞-sym { -∞} { -∞} = refl
⊓∞-sym { -∞} {[ x ]} = refl
⊓∞-sym { -∞} {+∞} = refl
⊓∞-sym {[ x ]} { -∞} = refl
⊓∞-sym {[ x ]} {[ y ]} = cong (λ x → [ x ]) (⊓-comm x y)
⊓∞-sym {[ x ]} {+∞} = refl
⊓∞-sym {+∞} { -∞} = refl
⊓∞-sym {+∞} {[ x ]} = refl
⊓∞-sym {+∞} {+∞} = refl

⊔∞-sym : ∀ {m n} → m ⊔∞ n ≡ n ⊔∞ m
⊔∞-sym { -∞} { -∞} = refl
⊔∞-sym { -∞} {[ x ]} = refl
⊔∞-sym { -∞} {+∞} = refl
⊔∞-sym {[ x ]} { -∞} = refl
⊔∞-sym {[ x ]} {[ y ]} = cong (λ x → [ x ]) (⊔-comm x y)
⊔∞-sym {[ x ]} {+∞} = refl
⊔∞-sym {+∞} { -∞} = refl
⊔∞-sym {+∞} {[ x ]} = refl
⊔∞-sym {+∞} {+∞} = refl

proof20 : ∀ {m n} → ¬ (suc m ≤ n) → ¬ (suc n ≤ m) → m ≡ n
proof20 {zero} {zero} p1 p2 = refl
proof20 {suc m} {zero} p1 p2 = n<1⇒n≡0 (≰⇒> p2)
proof20 {zero} {suc n} p1 p2 = sym (n<1⇒n≡0 (≰⇒> p1))
proof20 {suc m} {suc n} p1 p2 = ≤∧≮⇒≡ (≰⇒> (λ z → p2 (s≤s z))) p1

proof21 : ∀ {m n} → 1 ≤ m ⊔ n + 1
proof21 {m} {n} rewrite +-comm (m ⊔ n) 1 = s≤s z≤n

proof22,00 : ∀ {n} → n ≡ 1 → pred n ≡ 0
proof22,00 {n} p rewrite sym p = n∸n≡0 n

proof22,0 : ∀ {m n} → n - m ≤ 1 → suc m ≤ n → n -ᴺ suc m ≡ 0
proof22,0 {m} {n} p1 p2 rewrite m≤n⇒∣n-m∣≡n∸m (<⇒≤ p2) | sym (proof22,00 (≤-antisym p1 (m<n⇒0<n∸m p2))) = sym (pred[m∸n]≡m∸[1+n] n m)

proof22 : ∀ {m n} → n - m ≤ 1 → suc m ≤ n → n ≡ suc m
proof22 {m} {n} p1 p2 = ≤-antisym (m∸n≡0⇒m≤n (proof22,0 p1 p2)) p2
