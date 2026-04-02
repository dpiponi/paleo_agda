{-# OPTIONS --without-K --type-in-type #-}

module Section-2-2-7 where

 import Section-2-2-1
 open Section-2-2-1
 open Paths

 import Section-2-2-2
 open Section-2-2-2

 import Section-2-2-3
 open Section-2-2-3

 import Section-2-2-4
 open Section-2-2-4

 import tools
 open tools

 import Section-2-2-6
 open Section-2-2-6

 module 2-7 {A : Set} {P : A → Set} where

  module 2-7-2 where

   comp : {w w' : ∑ A P} → (w ≡ w') → ∑ (pr₁ w ≡ pr₁ w') (λ p → transport P p (pr₂ w) ≡ pr₂ w')
   comp refl = refl , refl

   pair= : {w w' : ∑ A P}
                 → ∑ (pr₁ w ≡ pr₁ w') (λ p → (p ∗)(pr₂ w) ≡ pr₂ w') → (w ≡ w')

   pair= {_ , _} {_ , _} (p , q) =
         j (λ w₁ w₁' p → {w₂ : P w₁} →  {w₂' : P w₁'} → ((p ∗) w₂ ≡ w₂') → (w₁ , w₂) ≡ (w₁' , w₂'))
           (λ w₁ q → ap (λ Q → (w₁ , Q)) q) -- tiny mod from book
           p q 

{-
   comp○pair≡id : {w w' : ∑ A P}
                   → (r : ∑ (pr₁ w ≡ pr₁ w') (λ p → transport P p (pr₂ w) ≡ pr₂ w'))
                   → comp {w} {w'} (pair= r) ≡ r
   comp○pair≡id {w₁ , w₂} {w₁' , w₂'} (p , q) =
                   j (λ w₁ w₁' p → (w₂ : P w₁) →  (w₂' : P w₁') → (q : (p ∗) w₂ ≡ w₂')
                        → comp {w₁ , w₂} {w₁' , w₂'} (pair= (p , q)) ≡ (p , q))
                     (λ w₁ w₂ w₂' q → j (λ _ _ q → comp {_ , _} {_ , _} (pair= (refl , q)) ≡ (refl , q))
                                        (λ x → refl)
                                        q)
                     p w₂ w₂' q 
-}

   comp○pair≡id : {w w' : ∑ A P}
                   → (r : ∑ (pr₁ w ≡ pr₁ w') (λ p → transport P p (pr₂ w) ≡ pr₂ w'))
                   → comp {w} {w'} (pair= r) ≡ r
   comp○pair≡id {w₁ , w₂} {.w₁ , .w₂} (refl , refl) = refl

   private gf≡id : {w w' : ∑ A P} → (p : w ≡ w') → pair= (comp p) ≡ p
           gf≡id {w} refl with w
           ... | (a , b) = refl

   private qinv-f : {w w' : ∑ A P} → qinv (comp {w} {w'})
           qinv-f {w} {w'} = (pair= , (comp○pair≡id {w} {w'} , gf≡id))

   theorem-2-7-2 :  {w w' : ∑ A P}
                   → (w ≡ w') ≃ ∑ (pr₁ w ≡ pr₁ w') (λ p → transport P p (pr₂ w) ≡ pr₂ w')
   theorem-2-7-2 = ( comp , qinv-to-isequiv comp qinv-f )

  theorem-2-7-2 = 2-7-2.theorem-2-7-2
  open 2-7-2

  corollary-2-7-3 : (z : ∑ A P) → z ≡ (pr₁ z , pr₂ z)
  corollary-2-7-3 z = 2-7-2.pair= (refl , refl)

  module 2-7-4 {Q : (∑ A P) → Set} where

    private R = λ x → ∑ (P x) (λ u → Q (x , u))

    theorem-2-7-4 : {x y : A} → (p : x ≡ y) → (u : P x) → (z : Q (x , u))
                  → (transport R p) (u , z) ≡ ((p ∗) u , transport Q (2-7-2.pair= (p , refl {P y} {(p ∗) u})) z)
    theorem-2-7-4 p = j (λ x y p → (u : P x) → (z : Q (x , u))
                  → (transport R p) (u , z) ≡ ((p ∗) u , transport Q (2-7-2.pair= (p , refl {P y} {(p ∗) u})) z))
                                (λ _ _ _ → refl)
                                p

  open 2-7-4
 open 2-7
 open 2-7-2 public