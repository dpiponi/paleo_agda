module infinitude-hpaste where

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

factor-or-prime : {n : ℕ} → (∃ λ p → suc (suc p) ∣ suc (suc n)) ⊎ Prime (suc (suc n)) 
factor-or-prime {n} = {! !}

factor-means-prime-factor : {n : ℕ} → (∃ λ p → suc (suc p) ∣ suc (suc n))
                                    → (∃ λ p → Prime (suc (suc p)) × suc (suc p) ∣ suc (suc n))
factor-means-prime-factor = {! !}

prime-means-prime-factor : {n : ℕ} → Prime (suc (suc n)) → (∃ λ p → Prime (suc (suc p)) × suc (suc p) ∣ suc (suc n))
prime-means-prime-factor {n} p = suc (suc n) , ({! !} , {! !})

prime-factor : {n : ℕ} → ∃ λ p → Prime (suc (suc p)) × suc (suc p) ∣ suc (suc n)
prime-factor {n} = [ factor-means-prime-factor {n} , prime-means-prime-factor {n} ] (factor-or-prime {n})
