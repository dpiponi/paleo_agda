 import Section-2-2-1
 open Section-2-2-1
 open Paths

 import Section-2-2-2
 open Section-2-2-2

 import Section-2-2-3
 open Section-2-2-3

 module Section-2-2-4 where
  _~_ : {A : Set} → {P : A → Set} → (f g : (x : A) → P x) → Set
  f ~ g = (x : _) → f x ≡ g x

  lemma-2-4-2-i : {A B : Set} → (f : A → B) → f ~ f
  lemma-2-4-2-i f x = refl

  lemma-2-4-2-ii : {A B : Set} → (f g : A → B) → (f ~ g) → (g ~ f)
  lemma-2-4-2-ii f g H x = (H x)⁻¹

  lemma-2-4-2-iii : {A B : Set} → (f g h : A → B) → (f ~ g) → (g ~ h) → (f ~ h)
  lemma-2-4-2-iii f g h H I x = H x ■ I x

  ap₂ : {A B C : Set} → (f : A → B → C) → {x y : A} → (x ≡ y) → {z w : B} → (z ≡ w) → (f x z ≡ f y w)
  ap₂ f {x} {y} p {z} {w} q = f x z ≡⟨ ap (λ Q → f x Q) q ⟩
                              f x w ≡⟨ ap (λ Q → f Q w) p ⟩
                              f y w
                              ▻

{-
  rightcancel : {A : Set} → {x y z : A} → (p q : x ≡ y) → (r : y ≡ z) → (p ■ r) ≡ (q ■ r) → p ≡ q
  rightcancel p q r α = p                ≡⟨ lemma-2-1-4-i-a ⟩
                        p ■ refl         ≡⟨ ap (λ Q → p ■ Q) ((lemma-2-1-4-iib r) ⁻¹) ⟩
                        p ■ (r ■ (r ⁻¹)) ≡⟨ lemma-2-1-4-iv p r (r ⁻¹) ⟩
                        (p ■ r) ■ (r ⁻¹) ≡⟨ ap (λ Q → Q ■ (r ⁻¹)) α ⟩
                        (q ■ r) ■ (r ⁻¹) ≡⟨ (lemma-2-1-4-iv q r (r ⁻¹))⁻¹ ⟩
                        q ■ (r ■ (r ⁻¹)) ≡⟨ ap (λ Q → q ■ Q) (lemma-2-1-4-iib r) ⟩
                        q ■ refl         ≡⟨ lemma-2-1-4-i-a ⁻¹ ⟩
                        q
                        ▻
-}

  rightcancel : {A : Set} → {x y z : A} → (p q : x ≡ y) → (r : y ≡ z) → (p ■ r) ≡ (q ■ r) → p ≡ q
  rightcancel refl refl refl x = refl


  lemma-2-4-3-0 : {A B : Set} → (f g : A → B) → (H : f ~ g) → {x : A}
                              → H x ■ ap g refl ≡ ap f refl ■ H x
  lemma-2-4-3-0 {A} {B} f g H {x} = ((lemma-2-1-4-i-a (H x))⁻¹) ■ (refl {f x ≡ g x} ■ lemma-2-1-4-i-b _)

 {-
  lemma-2-4-3 : {A B : Set} → (f g : A → B) → (H : f ~ g) → {x y : A} → (p : x ≡ y)
                            → H x ■ ap g p ≡ ap f p ■ H y
  lemma-2-4-3 f g H p = j (λ x y p → H x ■ ap g p ≡ ap f p ■ H y)
                          (λ x → lemma-2-4-3-0 f g H)
                          p
 -}

  lemma-2-4-3 : {A B : Set} → (f g : A → B) → (H : f ~ g) → {x y : A} → (p : x ≡ y)
                            → H x ■ ap g p ≡ ap f p ■ H y
  lemma-2-4-3 f g H refl = lemma-2-4-3-0 f g H
  hom-square = lemma-2-4-3

  corollary-2-4-4' : {A : Set} → (f : A → A) → (H : f ~ id {A}) → (x : A) → H (f x) ■ H x ≡ ap f (H x) ■ H x
  corollary-2-4-4' f H x = H (f x) ■ H x         ≡⟨ ap (λ Q → H (f x) ■ Q) ((lemma-2-2-iv (H x))⁻¹) ⟩
                           H (f x) ■ ap id (H x) ≡⟨ lemma-2-4-3 f id H (H x) ⟩
                           ap f (H x) ■ H x
                           ▻

  corollary-2-4-4 : {A : Set} → (f : A → A) → (H : f ~ id {A}) → (x : A) →  H (f x) ≡ ap f (H x)
  corollary-2-4-4 f H x = rightcancel _ _ _ (corollary-2-4-4' f H x)

  _×_ : Set → Set → Set
  A × B = ∑ A (λ _ → B)

  qinv : {A B : Set} → (f : A → B) → Set
  qinv {A} {B} f = ∑ (B → A) (λ g → ((f ○ g) ~ id) × ((g ○ f) ~ id))

  ex-2-4-7 : {A : Set} → qinv (id {A})
  ex-2-4-7 {A} = (id , ((λ x → refl) , (λ x → refl)))

  ex-2-4-8a : {A : Set} → {x y z : A} → {p : x ≡ y} → qinv (λ q → p ■ q)
  ex-2-4-8a {A} {x} {y} {z} {p} = ((λ q → (p ⁻¹) ■ q) , β , α)
                                  where α : (q : y ≡ z) → (p ⁻¹) ■ (p ■ q) ≡ q
                                        α q = (p ⁻¹) ■ (p ■ q) ≡⟨ lemma-2-1-4-iv (p ⁻¹) p q ⟩
                                              ((p ⁻¹) ■ p) ■ q ≡⟨ ap (λ Q → Q ■ q) (lemma-2-1-4-iia p) ⟩ 
                                              refl ■ q         ≡⟨ lemma-2-1-4-i-b _ ⁻¹ ⟩ 
                                              q
                                              ▻
                                        β : (q : x ≡ z) → p ■ ((p ⁻¹) ■ q) ≡ q
                                        β q = p ■ ((p ⁻¹) ■ q) ≡⟨ lemma-2-1-4-iv p (p ⁻¹) q ⟩
                                              (p ■ (p ⁻¹)) ■ q ≡⟨ ap (λ Q → Q ■ q) (lemma-2-1-4-iib p) ⟩ 
                                              refl ■ q         ≡⟨ lemma-2-1-4-i-b _ ⁻¹ ⟩ 
                                              q
                                              ▻
  ex-2-4-8b : {A : Set} → {x y z : A} → {p : x ≡ y} → qinv (λ q → q ■ p)
  ex-2-4-8b {A} {x} {y} {z} {p} = ((λ q → q ■ (p ⁻¹)) , β , α)
                                  where α : (q : z ≡ x) → (q ■ p) ■ (p ⁻¹) ≡ q
                                        α q = (q ■ p) ■ (p ⁻¹) ≡⟨ (lemma-2-1-4-iv q p (p ⁻¹))⁻¹ ⟩
                                              q ■ (p ■ (p ⁻¹)) ≡⟨ ap (λ Q → q ■ Q) (lemma-2-1-4-iib p) ⟩ 
                                              q ■ refl         ≡⟨ lemma-2-1-4-i-a _ ⁻¹ ⟩ 
                                              q
                                              ▻
                                        β : (q : z ≡ y) → (q ■ (p ⁻¹)) ■ p ≡ q
                                        β q = (q ■ (p ⁻¹)) ■ p ≡⟨ (lemma-2-1-4-iv q (p ⁻¹) p)⁻¹ ⟩
                                              q ■ ((p ⁻¹) ■ p) ≡⟨ ap (λ Q → q ■ Q) (lemma-2-1-4-iia p) ⟩ 
                                              q ■ refl         ≡⟨ lemma-2-1-4-i-a _ ⁻¹ ⟩ 
                                              q
                                              ▻
  ex-2-4-9 : {A : Set} → {x y : A} → (p : x ≡ y) → (P : A → Set) → qinv (transport P p)
  ex-2-4-9 {A} {x} {y} p P = (transport P (p ⁻¹) , β , α)
                         where α : (u : P x) → transport P (p ⁻¹) (transport P p u) ≡ u
                               α u = transport P (p ⁻¹) (transport P p u) ≡⟨ lemma-2-3-9 {A} {P} x y x p (p ⁻¹) u ⟩
                                     transport P (p ■ (p ⁻¹)) u ≡⟨ ap (λ Q → transport P Q u) (lemma-2-1-4-iib p) ⟩
                                     u
                                     ▻
                               β : (u : P y) → transport P p (transport P (p ⁻¹) u) ≡ u
                               β u = transport P p (transport P (p ⁻¹) u) ≡⟨ lemma-2-3-9 {A} {P} y x y (p ⁻¹) p u ⟩
                                     transport P ((p ⁻¹) ■ p) u ≡⟨ ap (λ Q → transport P Q u) (lemma-2-1-4-iia p) ⟩
                                     u
                                     ▻

  isequiv : {A B : Set} → (f : A → B) → Set
  isequiv {A} {B} f = (∑ (B → A) (λ g → (f ○ g) ~ id) × (∑ (B → A) (λ h → (h ○ f) ~ id)))

  qinv-to-isequiv : {A B : Set} → (f : A → B) → qinv f → isequiv f
  qinv-to-isequiv f (g , (α , β)) = ((g , α) , (g , β))

  isequiv-to-qinv : {A B : Set} → (f : A → B) → isequiv f → qinv f
  isequiv-to-qinv f ((g , α) , (h , β)) = (g , (α , β'))
                                          where γ : g ~ h
                                                γ u = ((β (g u))⁻¹) ■ ap h (α u)
                                                β' : (g ○ f) ~ id
                                                β' u = γ (f u) ■ β u

  _≃_ : (A B : Set) → Set
  A ≃ B = ∑ (A → B) (λ f → isequiv f)

  forward-map : {A B : Set} → {f : A → B} → isequiv f → (A → B)
  forward-map {A} {B} {f} e = f

  reverse-map : {A B : Set} → {f : A → B} → isequiv f → (B → A)
  reverse-map {A} {B} e = pr₁ (pr₁ e)

  lemma-2-4-12i : {A : Set} → isequiv (id {A})
  lemma-2-4-12i {A} = (id , (λ x → refl)) , id , (λ x → refl)

  lemma-2-4-12i' : (A : Set) → A ≃ A
  lemma-2-4-12i' A = (id , lemma-2-4-12i)

  lemma-2-4-12ii : {A B : Set} → A ≃ B → B ≃ A
  lemma-2-4-12ii (f , f-is-equiv) with isequiv-to-qinv f f-is-equiv
  lemma-2-4-12ii (f , f-is-equiv) | (f' , (α , β)) =
                                    (f' , qinv-to-isequiv f' (f , (β , α)))
  lemma-2-4-12iii : {A B C : Set} → A ≃ B → B ≃ C → A ≃ C
  lemma-2-4-12iii (f , f-is-equiv) (g , g-is-equiv) with isequiv-to-qinv f f-is-equiv
  lemma-2-4-12iii (f , f-is-equiv) (g , g-is-equiv) | (f' , (α , β)) with isequiv-to-qinv g g-is-equiv
  lemma-2-4-12iii {A} {B} {C} (f , f-is-equiv) (g , g-is-equiv) | (f' , (α , β)) | (g' , (γ , δ))
                  = (g ○ f , qinv-to-isequiv (g ○ f) ( f' ○ g' , ( μ , ν ) ))
                    where μ : (u : C) → g (f (f' (g' u))) ≡ u
                          μ u = g (f (f' (g' u))) ≡⟨ ap (λ Q → g Q) (α (g' u)) ⟩
                                g (g' u) ≡⟨ γ u ⟩
                                u
                                ▻
                          ν : (u : A) → f' (g' (g (f u))) ≡ u
                          ν u = f' (g' (g (f u))) ≡⟨ ap (λ Q → f' Q) (δ (f u)) ⟩
                                f' (f u)          ≡⟨ β u ⟩
                                u
                                ▻

