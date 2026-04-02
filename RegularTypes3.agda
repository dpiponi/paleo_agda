module RegularTypes3 where

module NatCat where

  open import Data.Nat
  open import Relation.Binary.PropositionalEquality
  open import Data.Fin hiding (_+_)
  open import Data.Sum public
  open import Function 
  
  split : ∀ {m n} -> Fin (m + n) -> Fin m ⊎ Fin n
  split {zero} i = inj₂ i
  split {suc n} zero = inj₁ zero
  split {suc n} (suc i) = map suc id (split i)
  
  glue : ∀ {m n} -> Fin m ⊎ Fin n -> Fin (m + n)
  glue {zero} (inj₁ ())
  glue {zero} (inj₂ y) = y
  glue {suc n} (inj₁ zero) = zero
  glue {suc n} (inj₁ (suc i)) = suc (glue {n} (inj₁ i))
  glue {suc n} (inj₂ y) = suc (glue {n} (inj₂ y))
  
  iso1 : ∀ {m n} (i : Fin (m + n)) -> glue {m} {n} (split i) ≡ i
  iso1 {zero} i = refl
  iso1 {suc n} zero = refl
  iso1 {suc n} (suc i) with split {n} i | iso1 {n} i
  iso1 {suc n}  (suc i) | inj₁ x | glueinj₁x≡i rewrite glueinj₁x≡i = refl
  iso1 {suc n'} (suc i) | inj₂ y | glueinj₂y≡i rewrite glueinj₂y≡i = refl 
  
  iso2 : ∀ {m n} (i : Fin m ⊎ Fin n) -> split {m} {n} (glue i) ≡ i
  iso2 {zero} (inj₁ ())
  iso2 {zero} (inj₂ y) = refl
  iso2 {suc n} (inj₁ zero) = refl
  iso2 {suc m} {n} (inj₁ (suc i)) rewrite iso2 {m} {n} (inj₁ i) = refl
  iso2 {suc m} {n} (inj₂ y) rewrite iso2 {m} {n} (inj₂ y) = refl
  
open import Data.Nat using (ℕ;zero;suc)
open import Data.Fin using (Fin;zero;suc)
open import Data.Vec
open import Data.Empty
open import Data.Product
open import Data.Sum
open import Data.Unit
open import Function
open import Data.Bool

Summation : Set → Set₁
Summation A = (A → Set) → Set

Σ# : {n : ℕ} -> (Fin n -> Set) -> Set
Σ# {zero} f = ⊥
Σ# {suc zero} f = f zero
Σ# {suc n} f = f zero ⊎ Σ# {n} λ i -> f (suc i)

--module Matrices {Ix : Set} {Σ : (Ix -> Set) -> Set} {_≈_ : Ix → Ix → Bool} where

record IndexSet : Set₁ where
  field
    carrier : Set
    ∑ : (carrier → Set) → Set
    _≈_ : carrier → carrier → Bool

Matrix : IndexSet → Set₁
Matrix I = IndexSet.carrier I → IndexSet.carrier I → Set

Id : {I : IndexSet} → Matrix I
Id {I} i j = if IndexSet._≈_ I i j then ⊤ else ⊥

Σ× : ∀ {Ix Iy : Set} → ((Ix → Set) → Set) → ((Iy → Set) → Set) → (Ix × Iy → Set) → Set
Σ× Σ₁ Σ₂ f =  Σ₁ (Σ₂ ∘ curry f)

prod-≈ : {Ix Iy : Set} → (Ix → Ix → Bool) → (Iy → Iy → Bool) → (Ix × Iy → Ix × Iy → Bool)
prod-≈ _≈_ _≋_ (x , y) (x' , y') = (x ≈ x') ∧ (y ≋ y')

_××_ : IndexSet → IndexSet → IndexSet
I ×× J = record {
         carrier = IndexSet.carrier I × IndexSet.carrier J ;
         ∑ = Σ× (IndexSet.∑ I) (IndexSet.∑ J) ;
         _≈_ = prod-≈ (IndexSet._≈_ I) (IndexSet._≈_ J)
  }

_⊕_ : ∀ {I J : IndexSet} → Matrix I → Matrix J → Matrix (I ×× J)
_⊕_ {I} {J} m n (i , i') (j , j') =
  (Id {I} i j × n i' j') ⊎ (m i j × Id {J} i' j')


data Poly {Coeffs : Set1} : Set1 where
  0p 1p : Poly 
  X : Poly
  _+_ _*_ : (D1 D2 : Poly {Coeffs}) -> Poly {Coeffs}
  K : Coeffs -> Poly

feq? : {n : ℕ} → Fin n → Fin n → Bool
feq? zero zero = true
feq? zero (suc _) = false
feq? (suc _) zero = false
feq? (suc m) (suc n) = feq? m n

F : ℕ → IndexSet
F n = record {
    carrier = Fin n ;
    ∑ = Σ# ;
    _≈_ = feq?
  }

Mat : ℕ → ℕ → Set → Set
Mat m n S = Vec (Vec S n) m
  
⟦_⟧ : {I : IndexSet} → Poly {Matrix I} -> Matrix I -> Matrix I
⟦ 0p ⟧ x i j = ⊥
⟦ 1p ⟧ x i j = ⊤
⟦ X ⟧ x i j = x i j
⟦_⟧ {I} (D1 + D2) x i j = (⟦_⟧ {I} D1 x i j) ⊎ (⟦_⟧ {I} D2 x i j)
⟦_⟧ {I} (D1 * D2) x i j = IndexSet.∑ I \ k -> (⟦_⟧ {I} D1 x i k) × (⟦_⟧ {I} D2 x k j)
⟦ K S ⟧ x i j = S i j
  
⟪_⟫ : Poly {Set} -> Set → Set
⟪ 0p ⟫ x = ⊥
⟪ 1p ⟫ x = ⊤
⟪ X ⟫ x = x
⟪ D1 + D2 ⟫ x = (⟪ D1 ⟫ x ⊎ ⟪ D2 ⟫ x)
⟪ D1 * D2 ⟫ x = (⟪ D1 ⟫ x × ⟪ D2 ⟫ x)
⟪ K S ⟫ x = S
  
data μ₁ (p : Poly) : Set where
  fix : ⟪ p ⟫ (μ₁ p) -> μ₁ p

data μ₂ {I : IndexSet} (p : Poly) (i j : IndexSet.carrier I) : Set where
  fix : ⟦ p ⟧ (μ₂ p) i j -> μ₂ p i j

{-
open Matrices
open OPlus

spin : Set → Matrix {Fin 1} {Σ#} {feq?}
spin a i j = lookup i (lookup j ((a ∷ []) ∷ []))

switch : Set → Matrix {Fin 2} {Σ#} {feq?}
switch a i j = lookup i (lookup j ((⊥ ∷ ⊥ ∷ []) ∷
                                   (a ∷ ⊥ ∷ []) ∷ []))

d : Set → Matrix {Fin 1 × Fin 2} {Σ× Σ# Σ#} {prod-≈ feq? feq?}
d a = _⊕_ {_} {_} {Σ#} {Σ#} {feq?} {feq?} (spin a) (switch ⊥)

-}