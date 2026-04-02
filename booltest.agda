module test where

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
