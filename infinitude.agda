module infinitude where

{-
open import Relation.Binary.PropositionalEquality
import Relation.Binary.EqReasoning 
open import Algebra
open import Algebra.Structures
open import Data.Nat.Properties
open import Function
open import Data.Product
open Relation.Binary.EqReasoning (setoid ℕ)
-}

open import Data.Nat.GCD
open import Data.Nat.LCM
open import Data.Product
open import Function
open import Data.Nat
open import Data.Product
open import Data.Sum
open import Data.Nat.Divisibility
open import Algebra.Structures
open import Relation.Binary.PropositionalEquality
open import Relation.Binary
import Relation.Binary.EqReasoning 

{-
data Prime : (n : ℕ) → Set where
  prime : {n : ℕ} → ({m : ℕ} → suc (suc m) ∣ suc (suc n) → suc (suc m) ≡ suc (suc n)) → Prime (suc (suc n))

lemma₁ : {m : ℕ} → suc (suc m) ∣ 2 → suc (suc m) ≤ 2
lemma₁ {m} = ∣⇒≤ {suc (suc m)} {1}

lemma₂ : {m : ℕ } → suc (suc m) ≤ 2 → m ≡ 0
lemma₂ {zero} p = refl
lemma₂ {suc n} (s≤s (s≤s ()))

theorem₁ : Prime 2
theorem₁ =  prime (λ p → cong (suc ∘ suc) (lemma₂ (lemma₁ p))) 

lemma₄ : {n : ℕ} → n < suc n
lemma₄ {zero} = s≤s z≤n
lemma₄ {suc n} = s≤s lemma₄

-- every integer has a prime factor?

lemma₃ : {m n : ℕ} → m < n → ∃ λ p → Prime (suc (suc p)) × suc (suc p) ∣ suc (suc m)
lemma₃ {m} {zero} = λ ()
lemma₃ {m} {suc n} = {!!}

theorem₂ : {n : ℕ} → ∃ λ p → Prime (suc (suc p)) × suc (suc p) ∣ suc (suc n)
theorem₂ {n} = lemma₃ {n} {suc n} lemma₄ 

-- every natural has some factor or is prime

lemma₆ : {n : ℕ} → n ∣ n
lemma₆ {n} = IsPreorder.reflexive (IsPartialOrder.isPreorder (Poset.isPartialOrder poset)) (_≡_.refl)

FACTOR : (n : ℕ) → Set
FACTOR (n) = (∃ λ p → suc (suc p) ∣ suc (suc n))
PRIME-FACTOR : (n : ℕ) → Set
PRIME-FACTOR n = (∃ λ p → Prime (suc (suc p)) × suc (suc p) ∣ suc (suc n))
PRIME : (n : ℕ) → Set
PRIME n = Prime (suc (suc n))

factor-or-prime : (n : ℕ) → FACTOR n ⊎ PRIME n
factor-or-prime n = {! !}

FACTOR-MEANS-PRIME-FACTOR : (n : ℕ) → Set
FACTOR-MEANS-PRIME-FACTOR n = FACTOR n → PRIME-FACTOR n
factor-means-prime-factor : (n : ℕ) → FACTOR-MEANS-PRIME-FACTOR n
factor-means-prime-factor n = {! !}

PRIME-MEANS-PRIME-FACTOR : (n : ℕ) → Set
PRIME-MEANS-PRIME-FACTOR n = PRIME n → PRIME-FACTOR n
prime-means-prime-factor : (n : ℕ) → PRIME-MEANS-PRIME-FACTOR n
prime-means-prime-factor n  = {! !}

prime-factor : (n : ℕ) → PRIME-FACTOR n
prime-factor n = [ factor-means-prime-factor n , prime-means-prime-factor n ] (factor-or-prime n)
-}

module test (A : Set) (B : Set) (C : Set) where
  f : {n : ℕ} → A → C
  f = {! !}
  g : {n : ℕ} → B → C
  g = {! !}
  h : {n : ℕ} → A ⊎ B → C
  h {n} = [ f {n} , g {n} ]