module weird where

data Test {A : Set} : A → Set where
  t : {a : A} → Test a

--a : Set
--a = {u : Test} → Test