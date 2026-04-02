module PropCalc3 where

open import Relation.Binary.PropositionalEquality

{-
data Nat : Set where
  zero : Nat
  suc : Nat → Nat
-}

--{-# BUILTIN NATURAL Nat #-}

data Bool : Set where
  false : Bool
  true : Bool

_&&_ : Bool → Bool → Bool
false && _ = false
true && x = x

_||_ : Bool → Bool → Bool
true || _ = true
false || x = x

!_ : Bool → Bool
! true = false
! false = true

open import Data.Nat

data prop : Set where
  Var : ℕ → prop
--  _∧_ : prop → prop → prop
  _∨_ : prop → prop → prop
  ¬_ : prop → prop

-- data Disjprop

Valuation = ℕ → Bool

⟦_⟧_ : prop → (ℕ → Bool) → Bool
⟦ Var n ⟧ φ = φ n
--⟦ a ∧ b ⟧ φ = ⟦ a ⟧ φ && ⟦ b ⟧ φ
⟦ a ∨ b ⟧ φ = ⟦ a ⟧ φ || ⟦ b ⟧ φ
⟦ ¬ a ⟧ φ = ! ⟦ a ⟧ φ

data _×_ (A : Set) (B : Set) : Set where
  _,_ : A → B → A × B

cong2 : {A B C : Set} -> {x y : A} -> {u v : B} → (f : A → B → C) -> x ≡ y -> u ≡ v → f x u ≡ f y v
cong2 f refl refl = refl

Fa&&!a : {a : Bool} → (a && (! a)) ≡ false
Fa&&!a {false} = refl
Fa&&!a {true} = refl

Ta||true : {a : Bool} → (a || true) ≡ true
Ta||true {false} = refl
Ta||true {true} = refl

--Fa∧¬a : {a : prop} → (φ : Valuation) → (⟦ (a ∧ ¬ a)⟧ φ) ≡ false
--Fa∧¬a {a} φ = Fa&&!a {⟦ a ⟧ φ}

data Maybe : (A : Set) → Set₁ where
  Just : {A : Set} → A → Maybe A
  Nothing : {A : Set} → Maybe A

PartialValuation : Set₁
PartialValuation = ℕ → Maybe Bool

isEq : ℕ → ℕ → Bool
isEq zero zero = true
isEq zero (suc _) = false
isEq (suc _) zero = false
isEq (suc a) (suc b) = isEq a b

data Extends? : PartialValuation → Set₁ where
  Extends : {n : ℕ} → {b : Bool} → {φ : PartialValuation} → (φ n ≡ Nothing) → Extends? φ
  Compatible : {n : ℕ} → {b : Bool} → {φ : PartialValuation} → (φ n ≡ Just b) → Extends? φ
  InCompatible : {n : ℕ} → {b : Bool} → {φ : PartialValuation} → (φ n ≡ Just (! b)) → Extends? φ

extend : ℕ → Bool → PartialValuation → PartialValuation
extend n b φ n' with isEq n n'
extend n b φ n' | false = φ n'
extend n b φ n' | true = Just b

data Close : (p : prop) → Set where
  Closed : {p : prop} → (∀ (φ : Valuation) → (⟦ p ⟧ φ) ≡ false) → Close p
  Open : {p : prop} → (φ : Valuation) → ⟦ p ⟧ φ ≡ true → Close p

thm1 : {p : prop} → {q : prop} → (∀ φ → (⟦ p ⟧ φ) ≡ (⟦ q ⟧ φ)) → Close p → Close q
thm1 {p} {q} r (Closed y) = Closed (λ φ → trans (sym (r φ)) (y φ))
thm1 {p} {q} r (Open φ y) = Open {q} φ (trans (sym (r φ)) y)

assoc-&& : ∀ {a b c : Bool} → ((a && b) && c ≡ a && (b && c))
assoc-&& {false} = refl
assoc-&& {true} = refl


open import Data.List
open import Data.List.All hiding (map)
open import Data.List.Any hiding (map)
open import Level
open Membership-≡

contradiction : prop → List prop
contradiction (Var i) = [ Var i ]
contradiction (a ∨ b) = contradiction a ++ contradiction b
contradiction (¬ (a ∨ b)) = contradiction (¬ a) ++ contradiction (¬ b)
contradiction (¬ ¬ a) = contradiction a
contradiction (¬ (Var i)) = [ ¬ (Var i)]

lemma1 : {a : Bool} → {b : Bool} → (! (a || b) ≡ true) → ! a ≡ true
lemma1 {false} p = refl
lemma1 {true} p = p

lemma2 : {a : Bool} → {b : Bool} → (! (a || b) ≡ true) → ! b ≡ true
lemma2 {false} p = p
lemma2 {true} {false} p = refl
lemma2 {true} {true} p = p

lemma3 : {a : Bool} → (! ! a ≡ true) → a ≡ true
lemma3 {false} x = x
lemma3 {true} x = refl

lemma4 : {a : Bool} → {b : Bool} → {q : Set} → (a || b ≡ true) → (a ≡ true → q) → (b ≡ true → q) → q
lemma4 {false} p f g = g p
lemma4 {true} p f g = f refl

data _ε_ : prop → prop → Set where
  id : {i : ℕ } → (Var i) ε (Var i)
  id-¬ : {i : ℕ } → (¬ Var i) ε (¬ Var i)
  ε-∧₁ : {p : prop} → {a : prop} → {b : prop} → p ε ¬ a → p ε ¬ (a ∨ b)
  ε-∧₂ : {p : prop} → {a : prop} → {b : prop} → p ε ¬ b → p ε ¬ (a ∨ b)
  ε-∨ : {p : prop} → {a : prop} → {b : prop} → p ε a → p ε b → p ε (a ∨ b)
  ε-¬ :  {p : prop} → {a : prop} → p ε a → p ε ¬ ¬ a

thm2 : {a : prop} → {b : prop} → {φ : Valuation} → a ε b → (⟦ b ⟧ φ) ≡ true → (⟦ a ⟧ φ) ≡ true
thm2 id q = q
thm2 id-¬ q = q
thm2 {p} {¬ (a ∨ b)} (ε-∧₁ y) q =  thm2 {p} {¬ a} y (lemma1 q)
thm2 {p} {¬ (a ∨ b)} {φ} (ε-∧₂ y) q = thm2 {p} {¬ b} y (lemma2 { ⟦ a ⟧ φ } q)
thm2 {p} {a ∨ b} (ε-∨ y y') q = lemma4 q (thm2 {p} {a} y) (thm2 {p} {b} y')
thm2 {p} {¬ ¬ a} (ε-¬ y) q = thm2 {p} {a} y (lemma3 q) 

lemma1' : {a : Bool} → {b : Bool} → ! a ≡ false → (! (a || b) ≡ false)
lemma1' {false} {false} p = p
lemma1' {true} {_} p = refl
lemma1' {false} {true} p = refl

lemma2' : {a : Bool} → {b : Bool} → ! b ≡ false → (! (a || b) ≡ false)
lemma2' {false} p = p
lemma2' {true} p = refl

lemma3' : {a : Bool} → (a ≡ false) → ! ! a ≡ false
lemma3' {false} x = x
lemma3' {true} x = x

lemma4' : {a : Bool} → {b : Bool} → (a ≡ false) → (b ≡ false) → (a || b ≡ false)
lemma4' {false} p q = q
lemma4' {true} p q = p

thm2a : {a : prop} → {b : prop} → {φ : Valuation} → a ε b → (⟦ a ⟧ φ) ≡ false → (⟦ b ⟧ φ) ≡ false
thm2a id q = q
thm2a id-¬ q = q
thm2a {p} {¬ (a ∨ b)} (ε-∧₁ y) q = lemma1' (thm2a y q)
thm2a {p} {¬ (a ∨ b)} {φ} (ε-∧₂ y) q = lemma2' { ⟦ a ⟧ φ } (thm2a y q)
thm2a {p} {a ∨ b} {φ} (ε-∨ y y') q = lemma4' {⟦ a ⟧ φ} (thm2a {p} {a} y q) ( thm2a {p} {b} y' q)
thm2a {p} {¬ ¬ a} {φ} (ε-¬ y) q = lemma3' (thm2a {p} {a} {φ} y q)

data Contradiction : prop → Set where
    contra-∨ : {a : prop} → {b : prop} → Contradiction a → Contradiction b → Contradiction (a ∨ b)
    contra-¬ : {a : prop} → Contradiction a → Contradiction (¬ ¬ a)
    contra-var₃ : {i : ℕ} → {a : prop} → (Var i) ε a → (¬ Var i) ε a → Contradiction a
    contra-∧₁ : {a : prop} → Contradiction (¬ a) → (b : prop) → Contradiction (¬ (a ∨ b))
    contra-∧₂ : (a : prop) → {b : prop} → Contradiction (¬ b) → Contradiction (¬ (a ∨ b))

elim₁ : {a : Bool} → { P : Set } → (a ≡ false → P) → (! a ≡ false → P) → P
elim₁ {false} p q = p refl
elim₁ {true} p q = q refl

elim₂ : {a : Bool} → { P : Set } → (! a ≡ false → P) → (a ≡ false → P) → P
elim₂ {false} p q = q refl
elim₂ {true} p q = p refl

-- BIG THEOREM
thm3 : {a : prop} → Contradiction a → {φ : Valuation} → ⟦ a ⟧ φ ≡ false
thm3 {a} (contra-var₃ {i} {.a} y y') {φ} =
       elim₁ {⟦ Var i ⟧ φ} lem4 lem6 where
         lem4 : ⟦ Var i ⟧ φ ≡ false → (⟦ a ⟧ φ) ≡ false
         lem4 p = thm2a {Var i} {a} {φ} y p
         lem6 : ⟦ ¬ Var i ⟧ φ ≡ false → (⟦ a ⟧ φ) ≡ false
         lem6 p = thm2a {¬ Var i} {a} {φ} y' p

thm3 (contra-∨ {a} {b} y y') {φ} = lemma4' {⟦ a ⟧ φ} (thm3 y) (thm3 y')
thm3 {¬ ¬ a} (contra-¬ y) {φ} = lemma3' {⟦ a ⟧ φ} (thm3 y)


-- ⟦ a ∧ b ∧ c ⟧ always false

-- ⟦ a ∧ b ⟧ always false

-- ⟦ a ⟧ φ = false

-- Break down ⟦ a ⟧ into list of props [a, b ∨ c, d, ...].

outer : {A : Set} → (A → A → A) → List A → List A → List A
outer _*_ [] _ = []
outer _*_ (a ∷ as) bs = map (_*_ a) bs ++ outer _*_ as bs

-- RTP ⟦ a ⟧ φ always false
-- then φ false for all lists in tableau a

⟪_⟫_ : List prop → Valuation → Bool
⟪ [] ⟫ _ = true
⟪ p ∷ ps ⟫ φ = (⟦ p ⟧ φ) || ⟪ ps ⟫ φ

tableau : prop → List (List prop)
tableau (Var i) = (Var i ∷ []) ∷ []
tableau (¬ Var i) = (¬ Var i ∷ []) ∷ []
tableau (¬ (a ∨ b)) = outer _++_ (tableau (¬ a)) (tableau (¬ b))
tableau (a ∨ b) = tableau a ++ tableau b
tableau (¬ ¬ a) = tableau a

a : prop
a = Var 0
b : prop
b = Var 1

test4 = tableau ((¬ (a ∨ ¬ a)) ∨ b)

{-
open import Relation.Nullary hiding (¬_)

data Inconsistent : List prop → Set where
  inconstent : {i : ℕ} → {props : List prop} → Var i ∈ props → ¬ Var i ∈ props → Inconsistent props

thm6 : {a : prop} → ({φ : Valuation} → ⟦ a ⟧ φ ≡ false) → All Inconsistent (tableau a)
thm6 {Var i} p with Data.List.Any.any (λ x → Dec (x ≡ (Var i ∷ []))) (tableau a)
thm6 {Var y} p | a = {!a !}
thm6 {¬ Var y} p = {!!}
thm6 {y ∨ y'} p = {!!}
thm6 {¬ (y ∨ y')} p = {!!}
thm6 {¬ ¬ a} p = {!thm6 {a} !}
-}

lemma10 : {a : Bool} → ! ! a ≡ false → a ≡ false
lemma10 {false} p = refl
lemma10 {true} p = p

lemma11 : {a : Bool} → {b : Bool} → a || b ≡ false → a ≡ false
lemma11 {false} p = refl
lemma11 {true} p = p

lemma12 : {a : Bool} → {b : Bool} → a || b ≡ false → b ≡ false
lemma12 {a} {false} p = refl
lemma12 {false} {true} p = p
lemma12 {true} {true} p = p

-- important : ({φ : Valuation} → ⟦ ¬ (a ∨ b) ⟧ φ == false) → 

-- BIG THEOREM 2
big : {a : prop} → ({φ : Valuation} → ⟦ a ⟧ φ ≡ false) → Contradiction a
big {Var i} p with p {λ i → true}
big {Var i} p | ()
big {¬ Var i} p with p {λ i → false}
big {¬ Var i} p | ()
big {¬ ¬ a} p =  contra-¬ (big {a} (λ {φ} →  lemma10 (p {φ})))
big {y ∨ y'} p = contra-∨ {y} {y'} (big {y} (λ {φ} → lemma11 (p {φ}))) ((big {y'} (λ {φ} → lemma12 {⟦ y ⟧ φ} (p {φ}))) )
big {¬ (y ∨ y')} p = {!!}
