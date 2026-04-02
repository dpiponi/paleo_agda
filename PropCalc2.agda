module PropCalc2 where

open import Relation.Binary.PropositionalEquality

data Nat : Set where
  zero : Nat
  suc : Nat → Nat

{-# BUILTIN NATURAL Nat #-}

data Bool : Set where
  false : Bool
  true : Bool

infixl 20 _||_
infixl 30 _&&_
infixl 40 !_
infixl 20 _∨_
infixl 30 _∧_
infixl 40 ¬_
infixl 10 ⟨_⟩_
infixl 10 ⟦_⟧_
infixl 10 [_]_

_&&_ : Bool → Bool → Bool
false && _ = false
true && x = x

_||_ : Bool → Bool → Bool
true || _ = true
false || x = x

!_ : Bool → Bool
! true = false
! false = true

mutual

  data ∧-prop : Set where
    ⊤ : ∧-prop
    _∧_ : ∨-prop → ∧-prop → ∧-prop

  data ∨-prop : Set where
    ⊥ : ∨-prop
    _∨_ : ¬-prop → ∨-prop → ∨-prop

  data ¬-prop : Set where
    ¬_ : ∧-prop → ¬-prop
    var : Nat → ¬-prop


Valuation = Nat → Bool

mutual
  [_]_ : ∧-prop → (Nat → Bool) → Bool
  [ ⊤ ] φ = true
  [ (a ∧ b) ] φ = (⟦ a ⟧ φ) && ([ b ] φ)

  ⟦_⟧_ : ∨-prop → (Nat → Bool) → Bool
  ⟦ ⊥ ⟧ φ = false
  ⟦ a ∨ b ⟧ φ = (⟨ a ⟩ φ) || (⟦ b ⟧ φ)

  ⟨_⟩_ : ¬-prop → (Nat → Bool) → Bool
  ⟨ ¬ a ⟩ φ = ! ([ a ] φ)
  ⟨ var i ⟩ φ = φ i


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

assoc-&& : ∀ {a b c : Bool} → ((a && b) && c ≡ a && (b && c))
assoc-&& {false} = refl
assoc-&& {true} = refl

data ∧-Closes? : (p : ∧-prop) → Set where
  Closed : {p : ∧-prop} → (∀ (φ : Valuation) → ([ p ] φ) ≡ false) → ∧-Closes? p
  Open : {p : ∧-prop} → (φ : Valuation) → [ p ] φ ≡ true → ∧-Closes? p

data ∨-Closes? : (p : ∨-prop) → Set where
  Closed : {p : ∨-prop} → (∀ (φ : Valuation) → (⟦ p ⟧ φ) ≡ false) → ∨-Closes? p
  Open : {p : ∨-prop} → (φ : Valuation) → ⟦ p ⟧ φ ≡ true → ∨-Closes? p

data ¬-Closes? : (p : ¬-prop) → Set where
  Closed : {p : ¬-prop} → (∀ (φ : Valuation) → (⟨ p ⟩ φ) ≡ false) → ¬-Closes? p
  Open : {p : ¬-prop} → (φ : Valuation) → ⟨ p ⟩ φ ≡ true → ¬-Closes? p

closes? : (ayes : List Nat) → (noes : List Nat) → (p : ¬-Proposition) → Closes? p
closes? (Var n) = Open (λ _ → true) refl

{-
close? (a ∨ b) with close? a | close? b
close? (a ∨ b) | Open φ p | _ = Open φ (cong (λ x → x || (⟦ b ⟧ φ)) p)
close? (a ∨ b) | Closed _ | Open ψ q = Open ψ ( trans (cong (λ y → (⟦ a ⟧ ψ) || y) q) (Ta||true { ⟦ a ⟧ ψ }))
close? (a ∨ b) | Closed p | Closed q = Closed ( (λ φ → cong2 _||_ (p φ) (q φ)) )
close? ((a ∧ b) ∧ c) = thm1 (λ φ → sym (assoc-&& {⟦ a ⟧ φ} {⟦ b ⟧ φ} {⟦ c ⟧ φ})) (close? (a ∧ (b ∧ c)))
close? _ = {! !}
-}

-- ∧-closes? : (p : ∧-prop) → Closes? p



{-
Fa∧¬a : {a : Proposition} → (φ : Valuation) → (⟦ (a ∧ ¬ a)⟧ φ) ≡ false
Fa∧¬a {a} φ = Fa&&!a {⟦ a ⟧ φ}
-}

{-
data Maybe : (A : Set) → Set₁ where
  Just : {A : Set} → A → Maybe A
  Nothing : {A : Set} → Maybe A

PartialValuation : Set₁
PartialValuation = Nat → Maybe Bool

isEq : Nat → Nat → Bool
isEq zero zero = true
isEq zero (suc _) = false
isEq (suc _) zero = false
isEq (suc a) (suc b) = isEq a b

data Extends? : PartialValuation → Set₁ where
  Extends : {n : Nat} → {b : Bool} → {φ : PartialValuation} → (φ n ≡ Nothing) → Extends? φ
  Compatible : {n : Nat} → {b : Bool} → {φ : PartialValuation} → (φ n ≡ Just b) → Extends? φ
  InCompatible : {n : Nat} → {b : Bool} → {φ : PartialValuation} → (φ n ≡ Just (! b)) → Extends? φ

extend : Nat → Bool → PartialValuation → PartialValuation
extend n b φ n' with isEq n n'
extend n b φ n' | false = φ n'
extend n b φ n' | true = Just b

data Close : (p : Proposition) → Set where
  Closed : {p : Proposition} → (∀ (φ : Valuation) → (⟦ p ⟧ φ) ≡ false) → Close p
  Open : {p : Proposition} → (φ : Valuation) → ⟦ p ⟧ φ ≡ true → Close p

thm1 : {p : Proposition} → {q : Proposition} → (∀ φ → (⟦ p ⟧ φ) ≡ (⟦ q ⟧ φ)) → Close p → Close q
thm1 {p} {q} r (Closed y) = Closed (λ φ → trans (sym (r φ)) (y φ))
thm1 {p} {q} r (Open φ y) = Open {q} φ (trans (sym (r φ)) y)
-}


{-
close? : (p : Proposition) → Close p
close? (Var n) = Open (λ _ → true) refl
close? (a ∨ b) with close? a | close? b
close? (a ∨ b) | Open φ p | _ = Open φ (cong (λ x → x || (⟦ b ⟧ φ)) p)
close? (a ∨ b) | Closed _ | Open ψ q = Open ψ ( trans (cong (λ y → (⟦ a ⟧ ψ) || y) q) (Ta||true { ⟦ a ⟧ ψ }))
close? (a ∨ b) | Closed p | Closed q = Closed ( (λ φ → cong2 _||_ (p φ) (q φ)) )
close? ((a ∧ b) ∧ c) = thm1 (λ φ → sym (assoc-&& {⟦ a ⟧ φ} {⟦ b ⟧ φ} {⟦ c ⟧ φ})) (close? (a ∧ (b ∧ c)))
close? _ = {! !}
-}