module imperative where

open import Data.Nat 

sum : ℕ → (ℕ → ℕ) → ℕ
sum 0 f = f 0
sum (suc n) f = f (suc n) + sum n f

id : ∀ {a : Set} → a → a
id = λ i → i

open import Relation.Binary.PropositionalEquality
open import Data.Product

lemma₁ : ∀ {n : ℕ} → suc n ≡ 1 + n
lemma₁ {n} = refl

import Relation.Binary.EqReasoning 
open import Algebra
open import Algebra.Structures
open import Data.Nat.Properties

theorem : ∀ (n : ℕ) → 2 * sum n id ≡ n * (1 + n)
theorem zero = refl
theorem (ℕ.suc n) =
  begin
    2 * sum (ℕ.suc n) id       ≡⟨ refl ⟩ 
      2 * (suc n + sum n id)     ≡⟨ proj₁ distrib 2 (suc n) (sum n id)⟩
      2 * suc n + 2 * sum n id   ≡⟨ cong (λ p → 2 * suc n + p) (theorem n)⟩
      2 * suc n + n * (1 + n)    ≡⟨ cong (λ p → 2 * p + n * (1 + n)) (lemma₁ {n})⟩
      2 * (1 + n) + n * (1 + n)  ≡⟨ sym (distribʳ (1 + n) 2 n) ⟩
      (2 + n) * (1 + n)          ≡⟨ comm *-isCommutativeMonoid (2 + n) (1 + n)⟩
      (1 + n) * (2 + n)          ≡⟨ refl ⟩
      suc n * (1 + suc n) ∎
  where open Relation.Binary.EqReasoning (setoid ℕ)
        open IsCommutativeSemiring isCommutativeSemiring using (distrib; distribʳ; *-isCommutativeMonoid)
        open IsCommutativeMonoid using (comm)
