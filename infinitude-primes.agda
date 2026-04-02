module infinitude-primes where

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

data FactorOrPrime (n : ℕ) : Set where
  IsPrime : Prime (suc (suc n)) → FactorOrPrime n
  HasFactor : (∃ λ p → suc (suc p) ∣ suc (suc n)) → FactorOrPrime n
  
factor-or-prime-up-to : (m : ℕ) → (n : ℕ) → m < n → FactorOrPrime m
factor-or-prime-up-to m zero ()
factor-or-prime-up-to m (suc n) (s≤s m≤n) = {! !}

factor-or-prime : {n : ℕ} → FactorOrPrime n
factor-or-prime {n} = {! !}


factor-means-prime-factor : {n : ℕ} → (∃ λ p → suc (suc p) ∣ suc (suc n))
                                    → (∃ λ p → Prime (suc (suc p)) × suc (suc p) ∣ suc (suc n))
factor-means-prime-factor = {! !}

prime-means-prime-factor : {n : ℕ} → Prime (suc (suc n)) → (∃ λ p → Prime (suc (suc p)) × suc (suc p) ∣ suc (suc n))
prime-means-prime-factor {n} p = suc (suc n) , ({! !} , {! !})

prime-factor : {n : ℕ} → ∃ λ p → Prime (suc (suc p)) × suc (suc p) ∣ suc (suc n)
prime-factor {n} with factor-or-prime {n}
prime-factor | IsPrime y = prime-means-prime-factor y
prime-factor | HasFactor y = factor-means-prime-factor y
