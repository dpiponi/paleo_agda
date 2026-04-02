module PrimeLattice where

{-
open import Relation.Binary
open import Relation.Binary.PropositionalEquality
open import Data.Bool
open import Level
open import Algebra
open import Algebra.Structures
open import Data.Product
import Algebra.FunctionProperties
open Algebra.FunctionProperties (_≡_)

rightIdentity : RightIdentity false _∨_ 
rightIdentity false = refl
rightIdentity true = refl

associative : Associative _∨_
associative false _ _ = refl
associative true _ _ = refl

Bool-∨ : Monoid zero zero
Bool-∨ = record {
   Carrier = Bool ;
   _≈_ = _≡_ ;
   _∙_ = _∨_ ;
   ε = false ;
   isMonoid = record {
    isSemigroup = record {
      isEquivalence = isEquivalence ;
        assoc = associative;
        ∙-cong = cong₂ _∨_
      } ;
      identity = (λ _ → refl) , rightIdentity
    }
 }
-}

open import Data.Nat.GCD
open import Data.Nat.LCM
open import Data.Product
open import Function
open import Data.Nat
open import Algebra.Structures
open import Relation.Binary.PropositionalEquality
import Relation.Binary.EqReasoning 

join : ℕ → ℕ → ℕ
join x y = proj₁ (lcm x y)
meet : ℕ → ℕ → ℕ
meet x y = proj₁ (gcd x y)

gcd-comm : ∀ {m n gcd : ℕ} → GCD m n gcd → GCD n m gcd
gcd-comm {m} {n} p = record {
         commonDivisor = swap (commonDivisor p)  ;
         greatest =  greatest p ∘ swap
         }
         where open GCD

∨-comm : ∀ (m n : ℕ) → meet m n ≡ meet n m
∨-comm m n   = let p = gcd m n
                   q = gcd n m
               in GCD.unique (proj₂ p) (gcd-comm (proj₂ q))

theorem : IsLattice _≡_  meet join
theorem = record {
        isEquivalence =  isEquivalence ;
        ∨-comm        = ∨-comm  ;
        ∨-assoc       = {! !} ;
        ∨-cong        = {! !} ;
        ∧-comm        = {! !} ;
        ∧-assoc       = {! !} ;
        ∧-cong        = {! !} ;
        absorptive    = {! !}
  }


-- theorem : IsLattice 

x = GCD 10 8 2


{-
So we have GCD m n g and GCD n m h
We have GCD m n g
        GCD m n h
RTP g ≡ h

-}