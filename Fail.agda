module Fail where

open import Data.Product

Σ× : ∀ {Ix Iy : Set} → ((Ix → Set) → Set) → ((Iy → Set) → Set) → (Ix × Iy → Set) → Set
Σ× Σ₁ Σ₂ f = {! Σ₂ (Σ₁ (curry f))!}
