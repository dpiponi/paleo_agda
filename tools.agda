{-# OPTIONS --without-K --type-in-type #-}

module tools where

 import Section-2-2-1
 open Section-2-2-1
 open Paths

 import Section-2-2-2
 open Section-2-2-2

 import Section-2-2-3
 open Section-2-2-3

 import Section-2-2-4
 open Section-2-2-4

 refl■p≡p : {A : Set} {x y : A} (p : x ≡ y) → refl ■ p ≡ p
 refl■p≡p p = (p≡refl■p _)⁻¹

{-
 on-left : {A B C : Set} (p : A ≡ B) (q : B ≡ C) → p ⁻¹ ■ p ■ q ≡ q
 on-left f = ap (λ Q → Q ◾ q) f
-}

 p⁻¹■p■q≡q : {A : Set} {x y z : A} (p : x ≡ y) (q : y ≡ z) → p ⁻¹ ■ p ■ q ≡ q
 p⁻¹■p■q≡q p q = p ⁻¹ ■ p ■ q ≡⟨ (■-assoc (p ⁻¹) p q) ⟩
                 (p ⁻¹ ■ p) ■ q ≡⟨ p⁻¹■p≡refl p ■r q ⟩
                 refl ■ q ≡⟨ refl■p≡p q ⟩
                 q
                 ▻

 p■p⁻¹■q≡q : {A : Set} {x y z : A} (p : y ≡ x) (q : y ≡ z) → p ■ p ⁻¹ ■ q ≡ q
 p■p⁻¹■q≡q p q = p ■ p ⁻¹ ■ q ≡⟨ (■-assoc p (p ⁻¹) q) ⟩
                 (p ■ p ⁻¹) ■ q ≡⟨ p■p⁻¹≡refl p ■r q ⟩
                 refl ■ q ≡⟨ refl■p≡p q ⟩
                 q
                 ▻

 p■q⁻¹■q≡p : {A : Set} {x y z : A} (p : x ≡ y) (q : z ≡ y) → p ■ q ⁻¹ ■ q ≡ p
 p■q⁻¹■q≡p p q = p ■ q ⁻¹ ■ q ≡⟨ p ■l (p⁻¹■p≡refl q) ⟩
                 p ■ refl ≡⟨ p■refl≡p p ⟩
                 p
                 ▻

 p■q■q⁻¹≡p : {A : Set} {x y z : A} (p : x ≡ y) (q : y ≡ z) → p ■ q ■ q ⁻¹ ≡ p
 p■q■q⁻¹≡p p q = p ■ q ■ q ⁻¹ ≡⟨ p ■l (p■p⁻¹≡refl q) ⟩
                 p ■ refl ≡⟨ p■refl≡p p ⟩
                 p
                 ▻

 p≡p■q■q⁻¹ : {A : Set} {x y z : A} (p : x ≡ y) (q : y ≡ z) → p ≡ p ■ q ■ q ⁻¹
 p≡p■q■q⁻¹ p q = (p■q■q⁻¹≡p p q)⁻¹


{-
 ap2 : {A B : Set} (f : A → B) {x y z : A} → (p : x ≡ y) → (q : y ≡ z)
                   → ap f (p ■ q) ≡ ap f p ■ ap f q
 ap2 f p q = ap f (p ■ q) ≡⟨ {!!} ⟩
              ap f p ■ ap f q
              ▻ 
-}

 ap3 : {A B : Set} (f : A → B) {x y z w : A} → (p : x ≡ y) → (q : y ≡ z) → (r : z ≡ w)
                   → ap f (p ■ q ■ r) ≡ ap f p ■ ap f q ■ ap f r
 ap3 f p q r = ap f (p ■ q ■ r) ≡⟨ ap-hom-second f p (q ■ r) ⟩
               ap f p ■ ap f (q ■ r) ≡⟨ ap f p ■l ap-hom-second f q r ⟩
               ap f p ■ ap f q ■ ap f r
               ▻
