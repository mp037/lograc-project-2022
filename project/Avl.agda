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
open import Data.Bool.Properties using (T?)
open import Data.Empty
open import Relation.Binary.Definitions
open import Agda.Builtin.Sigma
open import Data.Product

import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; sym; trans; cong; subst; resp)
open Eq.≡-Reasoning using (begin_; _≡⟨⟩_; step-≡; _∎)
open import Axiom.Extensionality.Propositional using (Extensionality)

postulate
  fun-ext : ∀ {a b} → Extensionality a b

{-
_<_ : ℕ → ℕ → Set
n < m = suc n ≤ m

_>_ : ℕ → ℕ → Set
n > m = m < n

infix 4 _<_
infix 4 _>_
-}

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

depth : {lower upper : ℕ∞} {h : ℕ} → Avl ℕ lower upper h → ℕ
depth {lower} {upper} {h} t = h


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

<-to-≤ : {n m : ℕ} → n < m → n ≤ m
<-to-≤ {zero} ( s≤s p) = z≤n
<-to-≤ {suc n} (s≤s p) = s≤s (<-to-≤ p)

<∞-trans : {n m k : ℕ∞} → n <∞ m → m <∞ k → n <∞ k
<∞-trans -∞<n      q         = -∞<n
<∞-trans ([]<[] p) ([]<[] q) = []<[] (≤-trans p (<-to-≤ q))
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


search : (x : ℕ) {lower upper : ℕ∞} {h : ℕ} → (t : Avl ℕ lower upper h) → (x ∈ t) ⊎ (¬ (x ∈ t))
search x (empty p) = inj₂ (λ ())
search x (node n l r p) with x <? n | x >? n
... | no ¬p | no ¬p₁ rewrite sym (x</n,x>/n⇒x≡n ¬p ¬p₁) = inj₁ here
... | no ¬p | yes p₁ = x∈r⇒x∈t p₁ (search x r)
... | yes p₁ | rez2 = x∈l⇒x∈t p₁ (search x l)


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
{-
proof13 : ∀ {m n o p} → m ≡ n ⊔ p → n ⊔ p + 1 + 1 ≡ suc (suc o) → m ⊔ n + 1 ⊔ (p ⊔ o + 1) ≡ n ⊔ p + 1
proof13 {m} {n} {o} {p} p1 p2 rewrite proof12 {m ⊔ n} {p ⊔ o} | p1 | ⊔-comm n p | sym (proof4,0 (proof4,0 p2))
    = cong (λ x → x + 1) (proof13,1 {p} {n})
-}

proof13 : ∀ {m n o p} → n ⊔ p + 1 ≡ suc m → n ⊔ p + 1 + 1 ≡ suc (suc o) → m ⊔ n + 1 ⊔ (p ⊔ o + 1) ≡ n ⊔ p + 1
proof13 {m} {n} {o} {p} p1 p2 rewrite proof12 {m ⊔ n} {p ⊔ o} | sym (proof4,0 p1) | ⊔-comm n p | sym (proof4,0 (proof4,0 p2)) 
    = cong (λ x → x + 1) (proof13,1 {p} {n})



leftRotation : {lower upper : ℕ∞} {h : ℕ} → AlmostAvlRight ℕ lower upper h → Avl ℕ lower upper (h -ᴺ 1)
leftRotation {lower} {upper} (almostrightnode {l = l₁} {r = r₁} n l (rightheavynode {l = l₂} {r = r₂} rn rl rr rx) x) rewrite proof1 (r₂ + 1) | sym (proof6 x rx)
    = node rn (node n l rl (proof8,1 x rx)) (subst (Avl ℕ [ rn ] upper) (proof6 x rx) rr) (proof10,2 x rx) 

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

leftRightRotation : {lower upper : ℕ∞} {h : ℕ}
                    → (n ln lrn : ℕ)
                    → (t1 : Avl ℕ lower [ ln ] (h + 1))
                    → (t2 : Avl ℕ [ ln ] [ lrn ] (h + 1))
                    → (t3 : Avl ℕ [ lrn ] [ n ] h)
                    → (t4 : Avl ℕ [ n ] upper (h + 1))
                    → Avl ℕ lower upper (h + 1 + 1 + 1)
leftRightRotation {lower} {upper} {h} n ln lrn t1 t2 t3 t4 = subst (Avl ℕ lower upper) (proof18 {h}) (node lrn (node ln t1 t2 (proof15 {h + 1})) (node n t3 t4 (proof16,01 {h})) (proof19 {h}))

leftRightRotation2 : {lower upper : ℕ∞} {h : ℕ}
                    → (n ln lrn : ℕ)
                    → (t1 : Avl ℕ lower [ ln ] (h + 1))
                    → (t2 : Avl ℕ [ ln ] [ lrn ] h)
                    → (t3 : Avl ℕ [ lrn ] [ n ] (h + 1))
                    → (t4 : Avl ℕ [ n ] upper (h + 1))
                    → Avl ℕ lower upper (h + 1 + 1 + 1)
leftRightRotation2 {lower} {upper} {h} n ln lrn t1 t2 t3 t4 = subst (Avl ℕ lower upper) (proof18,1 {h}) (node lrn (node ln t1 t2 (proof16,02 {h})) (node n t3 t4 (proof15 {h + 1})) (proof19,1 {h}))

rightLeftRotation : {lower upper : ℕ∞} {h : ℕ}
                    → (n rn rln : ℕ)
                    → (t1 : Avl ℕ lower [ n ] (h + 1))
                    → (t2 : Avl ℕ [ n ] [ rln ] (h + 1))
                    → (t3 : Avl ℕ [ rln ] [ rn ] h)
                    → (t4 : Avl ℕ [ rn ] upper (h + 1))
                    → Avl ℕ lower upper (h + 1 + 1 + 1)
rightLeftRotation {lower} {upper} {h} n rn rln t1 t2 t3 t4 = subst (Avl ℕ lower upper) (proof18 {h}) (node rln (node n t1 t2 (proof15 {h + 1})) (node rn t3 t4 (proof16,01 {h})) (proof19 {h}))

rightLeftRotation2 : {lower upper : ℕ∞} {h : ℕ}
                    → (n rn rln : ℕ)
                    → (t1 : Avl ℕ lower [ n ] (h + 1))
                    → (t2 : Avl ℕ [ n ] [ rln ] h)
                    → (t3 : Avl ℕ [ rln ] [ rn ] (h + 1))
                    → (t4 : Avl ℕ [ rn ] upper (h + 1))
                    → Avl ℕ lower upper (h + 1 + 1 + 1)
rightLeftRotation2 {lower} {upper} {h} n rn rln t1 t2 t3 t4 = subst (Avl ℕ lower upper) (proof18,1 {h}) (node rln (node n t1 t2 (proof16,02 {h})) (node rn t3 t4 (proof15 {h + 1})) (proof19,1 {h}))

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


almostAvlLeftTest : AlmostAvlLeft ℕ -∞ +∞ 3
almostAvlLeftTest = almostleftnode 3 (leftheavynode 2 (node 1 (empty -∞<n) (empty ([]<[] (s≤s (s≤s z≤n)))) z≤n) (empty ([]<[] (s≤s (s≤s (s≤s z≤n))))) refl) (empty n<+∞) refl 


data Tree (A : Set) (lower upper : ℕ∞) : ℕ → Set where
  emptytree : (p : lower <∞ upper) → Tree A lower upper zero
  nodetree : {l r : ℕ} → (n : ℕ)
            → Tree A lower [ n ] l
            → Tree A [ n ] upper r
            → Tree A lower upper ((l ⊔ r) + 1)

transform : {lower upper : ℕ∞} {h : ℕ} → Avl ℕ lower upper h → Tree ℕ lower upper h
transform (empty p) = emptytree p
transform (node n l r x) = nodetree n (transform l) (transform r)


isAlmostAvl : {lower upper : ℕ∞} {h : ℕ} → Tree ℕ lower upper h → Bool
isAlmostAvl (emptytree p) = false
isAlmostAvl (nodetree {l = l₁} {r = r₁} n l r) with (l₁ - r₁) 
... | zero = false
... | suc zero = false
... | suc (suc p) = true


isLeftLeaning : {lower upper : ℕ∞} {h : ℕ} → Avl ℕ lower upper h → Bool
isLeftLeaning (empty p) = false
isLeftLeaning (node {l = l₁} {r = r₁} n l r x) = r₁ <ᵇ l₁

isRightLeaning : {lower upper : ℕ∞} {h : ℕ} → Avl ℕ lower upper h → Bool
isRightLeaning (empty p) = false
isRightLeaning (node {l = l₁} {r = r₁} n l r x) = l₁ <ᵇ r₁

isLeftLeaning2 : {lower upper : ℕ∞} {h x1 x2 : ℕ} → 0 < h → Avl ℕ lower upper h → Dec (x1 < x2)
isLeftLeaning2 p (node {l = l₁} {r = r₁} n l r x) = {! r₁ <? l₁  !}



_⊓∞_ : (m n : ℕ∞) → ℕ∞
-∞ ⊓∞ _ = -∞
[ x ] ⊓∞ -∞ = -∞
[ x ] ⊓∞ [ x1 ] = [ (x ⊓ x1) ]
[ x ] ⊓∞ +∞ = [ x ]
+∞ ⊓∞ n = n

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

_⊔∞_ : (m n : ℕ∞) → ℕ∞
-∞ ⊔∞ n = n
[ x ] ⊔∞ -∞ = [ x ]
[ x ] ⊔∞ [ x1 ] = [ (x ⊔ x1) ]
[ x ] ⊔∞ +∞ = +∞
+∞ ⊔∞ n = +∞

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


proof9,0rev : ∀ {m n} → m < n → [ m ] <∞ [ n ]
proof9,0rev {m} {n} p = []<[] p

proof9 : ∀ {m n} → m <∞ n → (n ⊓∞ m) <∞ n
proof9 { -∞} { -∞} p = p
proof9 { -∞} {[ x ]} p = p
proof9 { -∞} {+∞} p = p
proof9 {[ x ]} {[ y ]} p rewrite ⊓-comm y x | m≤n⇒m⊓n≡m (<⇒≤ ([]<[]⇒< p)) = p
proof9 {[ x ]} {+∞} p = p
proof9 {+∞} {+∞} p = p

--proof9sym : ∀ {m n} → m <∞ n → (m ⊓∞ n) <∞ n
--proof9sym {m} {n} p = {!   !}

[]<∞n⇒[]⊔∞n≡n : ∀ {m n} → [ m ] <∞ n → [ m ] ⊔∞ n ≡ n
[]<∞n⇒[]⊔∞n≡n {m} {[ x ]} p rewrite m≤n⇒m⊔n≡n (<⇒≤ ([]<[]⇒< p)) = refl
[]<∞n⇒[]⊔∞n≡n {m} {+∞} p = refl

[]<∞n⇒[]<∞[]⊔∞n : ∀ {m n} → [ m ] <∞ n → [ m ] <∞ ([ m ] ⊔∞ n)
[]<∞n⇒[]<∞[]⊔∞n {m} {n} p rewrite []<∞n⇒[]⊔∞n≡n p = p

n<∞[]⇒[]⊓∞n≡n : ∀ {m n} → n <∞ [ m ] → [ m ] ⊓∞ n ≡ n
n<∞[]⇒[]⊓∞n≡n {m} { -∞} p = refl
n<∞[]⇒[]⊓∞n≡n {m} {[ x ]} p rewrite m≥n⇒m⊓n≡n (<⇒≤ ([]<[]⇒< p)) = refl


data InsertTree (lower upper : ℕ∞) : Set where
  avl : {l r : ℕ} → (n : ℕ)
        → Avl ℕ lower [ n ] l
        → Avl ℕ [ n ] upper r
        → r - l ≤ 1
        → InsertTree lower upper
  llRot : {h : ℕ} → (n ln : ℕ)
          → Avl ℕ lower [ ln ] (h + 1)
          → Avl ℕ [ ln ] [ n ] h
          → Avl ℕ [ n ] upper h
          → InsertTree lower upper
  rrRot : {h : ℕ} → (n rn : ℕ)
          → (t1 : Avl ℕ lower [ n ] h)
          → (t2 : Avl ℕ [ n ] [ rn ] h)
          → (t3 : Avl ℕ [ rn ] upper (h + 1))
          → InsertTree lower upper
  lrRotL : {h : ℕ} → (n ln lrn : ℕ)
            → Avl ℕ lower [ ln ] (h + 1)
            → Avl ℕ [ ln ] [ lrn ] (h + 1)
            → Avl ℕ [ lrn ] [ n ] h
            → Avl ℕ [ n ] upper (h + 1)
            → InsertTree lower upper
  lrRotR : {h : ℕ} → (n ln lrn : ℕ)
            → Avl ℕ lower [ ln ] (h + 1)
            → Avl ℕ [ ln ] [ lrn ] h
            → Avl ℕ [ lrn ] [ n ] (h + 1)
            → Avl ℕ [ n ] upper (h + 1)
            → InsertTree lower upper
  rlRotL : {h : ℕ} → (n rn rln : ℕ)
            → Avl ℕ lower [ n ] (h + 1)
            → Avl ℕ [ n ] [ rln ] (h + 1)
            → Avl ℕ [ rln ] [ rn ] h
            → Avl ℕ [ rn ] upper (h + 1)
            → InsertTree lower upper
  rlRotR : {h : ℕ} → (n rn rln : ℕ)
            → Avl ℕ lower [ n ] (h + 1)
            → Avl ℕ [ n ] [ rln ] h
            → Avl ℕ [ rln ] [ rn ] (h + 1)
            → Avl ℕ [ rn ] upper (h + 1)
            → InsertTree lower upper

testTree1 : Avl ℕ -∞ [ 4 ] 2
testTree1 = node 2 (node 1 (empty -∞<n) (empty ([]<[] (s≤s (s≤s z≤n)))) z≤n) (empty ([]<[] (s≤s (s≤s (s≤s z≤n))))) (s≤s z≤n)

testTree2 : Avl ℕ [ 4 ] +∞ 1
testTree2 = node 5 (empty ([]<[] (s≤s (s≤s (s≤s (s≤s (s≤s z≤n))))))) (empty n<+∞) z≤n

testInsertTree : InsertTree -∞ +∞
testInsertTree = avl 4 testTree1 testTree2 (s≤s z≤n)

proof20 : ∀ {m n} → ¬ (suc m ≤ n) → ¬ (suc n ≤ m) → m ≡ n
proof20 {zero} {zero} p1 p2 = refl
proof20 {suc m} {zero} p1 p2 = n<1⇒n≡0 (≰⇒> p2)
proof20 {zero} {suc n} p1 p2 = sym (n<1⇒n≡0 (≰⇒> p1))
proof20 {suc m} {suc n} p1 p2 = ≤∧≮⇒≡ (≰⇒> (λ z → p2 (s≤s z))) p1

proof21 : ∀ {m n} → 1 ≤ m ⊔ n + 1
proof21 {m} {n} rewrite +-comm (m ⊔ n) 1 = s≤s z≤n



{-
insert'2 : {lower upper : ℕ∞} {h : ℕ} → (x : ℕ) → Avl ℕ lower upper h → (p1 : lower <∞ [ x ]) → (p2 : [ x ] <∞ upper) → InsertTree
insert'2 x (empty p) p1 p2 = avl x (empty p1) (empty p2) z≤n
insert'2 x (node {l = l₁} {r = r₁} n l r p) p1 p2 with x <? n | x >? n
insert'2 x (node {l = l₁} {r = r₁} n l r p) p1 p2 | no ¬p | no ¬p₁ rewrite sym (x</n,x>/n⇒x≡n ¬p ¬p₁) = avl {l = l₁} {r = r₁} x l r p
insert'2 x (node {l = l₁} {r = r₁} n l r p) p1 p2 | false because proof₁ | yes p₁ = {!   !}
insert'2 x (node {l = l₁} {r = r₁} n l r p) p1 p2 | yes p₁ | rez2 = {!   !}
-}


insert : {lower upper : ℕ∞} {h : ℕ} → (x : ℕ) → Avl ℕ lower upper h → (p1 : lower <∞ [ x ]) → (p2 : [ x ] <∞ upper) → Σ[ h' ∈ ℕ ] ((Avl ℕ ([ x ] ⊓∞ lower) ([ x ] ⊔∞ upper) h') × ((h' ≡ h) ⊎ (h' ≡ suc h)) × (0 < h'))

insert' : {lower upper : ℕ∞} {h : ℕ} → (x : ℕ) → Avl ℕ lower upper h → (p1 : lower <∞ [ x ]) → (p2 : [ x ] <∞ upper) → InsertTree lower upper
insert' x (empty p) p1 p2 = avl x (empty p1) (empty p2) z≤n
insert' x (node {l = l₁} {r = r₁} n l r p) p1 p2 with x <? n | x >? n
insert' x (node {l = l₁} {r = r₁} n l r p) p1 p2 | no ¬p | no ¬p₁ rewrite sym (x</n,x>/n⇒x≡n ¬p ¬p₁) = avl {l = l₁} {r = r₁} x l r p
insert' x (node {l = l₁} {r = r₁} n l r p) p1 p2 | no ¬p | yes p₁ with newT
    where newT = insert x r ([]<[] p₁) p2
insert' x (node {l = l₁} {r = r₁} n l r p) p1 p2 | no ¬p | yes p₁ | fst₁ , fst₂ , inj₁ x₁ , snd₁ rewrite m≥n⇒m⊓n≡n (<⇒≤ p₁) | []<∞n⇒[]⊔∞n≡n p2 | sym x₁ = avl n l fst₂ p
insert' x (node {l = l₁} {r = r₁} n l r p) p1 p2 | no ¬p | yes p₁ | fst₁ , fst₂ , inj₂ y , snd₁ with fst₁ - l₁ ≤? 1
insert' x (node {l = l₁} {r = r₁} n l r p) p1 p2 | no ¬p | yes p₁ | .(d1 ⊔ d2 + 1) , node {l = d1} {r = d2} n₁ fst₂ fst₃ x₁ , inj₂ y , snd₁ | no ¬p₁ = {!   !}
insert' x (node {l = l₁} {r = r₁} n l r p) p1 p2 | no ¬p | yes p₁ | fst₁ , fst₂ , inj₂ y , snd₁ | yes p₂ rewrite m≥n⇒m⊓n≡n (<⇒≤ p₁) | []<∞n⇒[]⊔∞n≡n p2 = avl n l fst₂ p₂
insert' x (node {l = l₁} {r = r₁} n l r p) p1 p2 | yes p₁ | rez2 = {!   !}




insert x (empty p) p1 p2 = 1 , (node x (empty (proof9 p1)) (empty ([]<∞n⇒[]<∞[]⊔∞n p2)) z≤n) ,′ inj₂ refl ,′ s≤s z≤n
insert {lower} {upper} {h} x (node {l = l₁} {r = r₁} n l r p) p1 p2 with x <? n | x >? n
... | no ¬p | no ¬p₁ rewrite proof20 ¬p₁ ¬p = h , (node x (subst (λ y → Avl ℕ y [ x ] l₁) (sym (n<∞[]⇒[]⊓∞n≡n p1)) l) (subst (λ y → Avl ℕ [ x ] y r₁) (sym ([]<∞n⇒[]⊔∞n≡n p2)) r) p) ,′ inj₁ refl ,′ proof21 {l₁} {r₁}
... | no ¬p | yes p₁ = {!   !}
... | yes p₁ | rez2 = {!   !}

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



              