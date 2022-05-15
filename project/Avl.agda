module Avl where

open import Agda.Builtin.Nat using () renaming (_-_ to _-ᴺ_)
open import Data.Nat using (ℕ; zero; suc; _+_; _*_; _≤_; _≤ᵇ_; _<ᵇ_; _≥_; _<_; z≤n; s≤s; _⊔_; compare; _⊓_) renaming (∣_-_∣ to _-_)
open import Data.Nat.Properties
open import Data.List using (List; []; _∷_; length)
open import Data.Bool.Base using (T; if_then_else_)
open import Agda.Builtin.Bool public
open import Data.Maybe
open import Data.Sum.Base

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

{-
minuszero : (n : ℕ) → n - 0 ≡ n
minuszero zero = refl
minuszero (suc n) = refl

treeDepth : ℕ → Maybe ℕ
treeDepth zero = just zero
treeDepth (suc zero) = just 1
treeDepth (suc (suc n)) = nothing

isjust : Maybe ℕ → Bool
isjust (just x) = true
isjust nothing = false


goodDepth : {a b : ℕ} → (isjust (treeDepth (b - a)) ≡ true) ≡ (b - a ≤ 1)
goodDepth {a} {b} with (b - a) 
... | zero = {!   !}
... | suc p = {!   !}


abszero : (n : ℕ) → n - n ≡ 0
abszero zero = refl
abszero (suc n) = abszero n


rightRotation2 : {lower upper : ℕ∞} {rh h : ℕ} 
                → (n : ℕ) 
                → Avl2 ℕ lower [ k ] suc (suc rh)
                → Avl2 ℕ [ k ] upper rh
                → Avl2 

_1?+⟨_⟩ : ∀ {l} (T : ℕ → Set l) → ℕ → Set l
T 1?+⟨ n ⟩ = ∃[ inc ] T (if inc
                            then suc n 
                            else n)

                          

pattern 0+_ tr = false tr
pattern 1+_ tr = true tr




data 0or1 : Set where
  zero : 0or1
  one : 0or1

rightRotation2 : {lower upper : ℕ∞} {h : ℕ}
                → (n : ℕ)
                → Avl2 ℕ lower [ n ] (suc (suc h))
                → Avl2 ℕ [ n ] upper h
                → Avl2 ℕ lower upper (suc (suc h))
rightRotation2 n (node2 nr ll lr x) rt = node2 nr ll (node2 n lr rt {!   !}) {!   !}
-}

{-
data Avl2 (A : Set) (lower upper : ℕ∞) : ℕ → Set where --the last element is the height of the tree
  empty2 : (p : lower <∞ upper) → Avl2 A lower upper zero
  node2 : {l r h : ℕ} → (n : ℕ)
            → Avl2 A lower [ n ] l
            → Avl2 A [ n ] upper r
            → ⟨ l ⊔ r ⟩≡ h
            → Avl2 A lower upper (suc h)

data ⟨_⊔_⟩≡_ : ℕ → ℕ → ℕ → Set where
  lef : ∀ {n} → ⟨ suc n ⊔ n ⟩≡ suc n
  cen : ∀ {n} → ⟨ n ⊔ n ⟩≡ n
  rig : ∀ {n} → ⟨ n ⊔ suc n ⟩≡ suc n

test1 : Avl2 ℕ -∞ +∞ 1
test1 = node2 5 (empty2 -∞<n) (empty2 n<+∞) cen
-}


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
            → LeftHeavyAvl A lower [ n ] l
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



leftRotation : {lower upper : ℕ∞} {h : ℕ} → AlmostAvlRight ℕ lower upper h → Avl ℕ lower upper (h -ᴺ 1)
leftRotation {lower} {upper} (almostrightnode {l = l₁} {r = r₁} n l (rightheavynode {l = l₂} {r = r₂} rn rl rr rx) x) rewrite proof1 (r₂ + 1) | sym (proof6 x rx)
    = node rn (node n l rl (proof8,1 x rx)) (subst (Avl ℕ [ rn ] upper) (proof6 x rx) rr) (proof10,2 x rx) 


rightRotation : {lower upper : ℕ∞} {h : ℕ} → AlmostAvlLeft ℕ lower upper h → Avl ℕ lower upper (h -ᴺ 1)
rightRotation {lower} (almostleftnode {l = l₁} {r = r₁} n (leftheavynode {l = l₂} {r = r₂} ln ll lr lx) r x) rewrite proof1 (l₂ + 1) | sym (proof6,2 x lx) 
    = node {l = l₂} {r = r₂ ⊔ r₁ + 1} ln (subst (Avl ℕ lower [ ln ]) (proof6,2 x lx) ll) (node n lr r (proof8 x lx)) (proof10 x lx)
    


testcomp : (m n : ℕ) → Bool
testcomp m n with compare m n
... | Data.Nat.less .m k = {!   !}
... | Data.Nat.equal .m = {!   !}
... | Data.Nat.greater .n k = {!   !}

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

{-
isLeftLeaning : {lower upper : ℕ∞} {h : ℕ} → Tree ℕ lower upper h → Bool
isLeftLeaning (emptytree p) = false
isLeftLeaning (nodetree {l = l₁} {r = r₁} n l r) = r₁ <ᵇ l₁

isRightLeaning : {lower upper : ℕ∞} {h : ℕ} → Tree ℕ lower upper h → Bool
isRightLeaning (emptytree p) = false
isRightLeaning (nodetree {l = l₁} {r = r₁} n l r) = l₁ <ᵇ r₁
-}


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

proof9,0 : ∀ {m n} → [ m ] <∞ [ n ] → m < n
proof9,0 {m} {n} ([]<[] x) = x

proof9,0rev : ∀ {m n} → m < n → [ m ] <∞ [ n ]
proof9,0rev {m} {n} p = []<[] p

proof9 : ∀ {m n} → m <∞ n → (n ⊓∞ m) <∞ n
proof9 { -∞} { -∞} p = p
proof9 { -∞} {[ x ]} p = p
proof9 { -∞} {+∞} p = p
proof9 {[ x ]} {[ y ]} p rewrite ⊓-comm y x | m≤n⇒m⊓n≡m (<⇒≤ (proof9,0 p)) = p
proof9 {[ x ]} {+∞} p = p
proof9 {+∞} {+∞} p = p

--proof9sym : ∀ {m n} → m <∞ n → (m ⊓∞ n) <∞ n
--proof9sym {m} {n} p = {!   !}

[]<∞n⇒[]⊔∞n≡n : ∀ {m n} → [ m ] <∞ n → [ m ] ⊔∞ n ≡ n
[]<∞n⇒[]⊔∞n≡n {m} {[ x ]} p rewrite m≤n⇒m⊔n≡n (<⇒≤ (proof9,0 p)) = refl
[]<∞n⇒[]⊔∞n≡n {m} {+∞} p = refl

[]<∞n⇒[]<∞[]⊔∞n : ∀ {m n} → [ m ] <∞ n → [ m ] <∞ ([ m ] ⊔∞ n)
[]<∞n⇒[]<∞[]⊔∞n {m} {n} p rewrite []<∞n⇒[]⊔∞n≡n p = p



insert : {lower upper : ℕ∞} {h : ℕ} → (x : ℕ) → Avl ℕ lower upper h → (p1 : lower <∞ [ x ]) → (p2 : [ x ] <∞ upper) → (Avl ℕ ([ x ] ⊓∞ lower) ([ x ] ⊔∞ upper) h) ⊎ (Avl ℕ ([ x ] ⊓∞ lower) ([ x ] ⊔∞ upper) (suc h))
insert x (empty p) p1 p2 = inj₂ (node x (empty (proof9 p1)) (empty ([]<∞n⇒[]<∞[]⊔∞n p2))  z≤n)
insert {lower} {upper} x (node n l r p) p1 p2 with compare x n
... | Data.Nat.less .x k = {!   !}
... | Data.Nat.equal .x = inj₁ (node n {! (subst ? ? ?) !} {! r  !} p)
... | Data.Nat.greater .n k = {!   !}
--insert x (empty p) = inj₂ (node x (empty {!   !}) {!   !} {!   !}) 
--insert x (node n t t₁ x₁) = {!   !}



--AVL N = Avl N -inf +inf


       