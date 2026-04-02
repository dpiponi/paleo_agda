module Example where

--open import Data.Nat
open import Data.Fin
open import Relation.Binary.PropositionalEquality

--prf : ∀ n m → (n + m) + n ≡ m + (n + n)
--prf n m = {!!}

data Expr n : Set where
  var : Fin n → Expr n
  _⊕_ : Expr n -> Expr n -> Expr n
  zero : Expr n

norm : ∀ {n} → Expr n → Expr n
norm = reify ∘ eval

eval : ∀ {n} → Expr n → NF n
reify : ∀ {n} → NF n → Expr n

NF : ℕ → Set
NF n = Vec ℕ n

data Eqn n : Set where
  _==_ : Expr n → Expr n → Eqn n