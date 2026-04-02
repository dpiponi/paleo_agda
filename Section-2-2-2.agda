{-# OPTIONS --without-K --type-in-type #-}

 module Section-2-2-2 where
  import Section-2-2-1
  open Section-2-2-1
  open Paths


  lemma-2-2-2-i : {A B : Set} → (f : A → B) → {x y z : A} → (p : x ≡ y) → {q : y ≡ z}
                   → ap f (p ■ q) ≡ ap f p ■ ap f q
  lemma-2-2-2-i f refl {refl} = refl
  ap-hom-second : {A B : Set} → (f : A → B) → {x y z : A} → (p : x ≡ y) → (q : y ≡ z)
                   → ap f (p ■ q) ≡ ap f p ■ ap f q
  ap-hom-second f p q = lemma-2-2-2-i f p {q}

  lemma-2-2-2-ii : {A B : Set} → (f : A → B) → {x y : A} → (p : x ≡ y)
                 → ap f (p ⁻¹) ≡ (ap f p) ⁻¹
  lemma-2-2-2-ii f refl = refl
  ap-inv-second : {A B : Set} → (f : A → B) → {x y : A} → (p : x ≡ y)
                 → ap f (p ⁻¹) ≡ (ap f p) ⁻¹
  ap-inv-second = lemma-2-2-2-ii

  -- composition
  _○_ : {A B C : Set} → (B → C) → (A → B) → A → C
  g ○ f = λ x → g (f x)


  _□ : (p : Set) → p → p
  p □ = id

  _→⟨_⟩_ : {q r : Set} → (p : Set) → (p → q) → (q → r) → (p → r)
  p →⟨ α ⟩ β = β ○ α

 {-
  lemma-2-2-iii-0 : {A B C : Set} → (f : A → B) → (g : B → C)
                 → {x : A}
                 → ap g (ap f (refl' x)) ≡ ap (g ○ f) (refl' x)
  lemma-2-2-iii-0 f g = refl

  lemma-2-2-iii : {A B C : Set} → (f : A → B) → (g : B → C)
                 → {x y : A} → (p : x ≡ y)
                 → ap g (ap f p) ≡ ap (g ○ f) p
  lemma-2-2-iii f g p = j (λ x y p → ap g (ap f p) ≡ ap (g ○ f) p)
                          (λ x → lemma-2-2-iii-0 f g)
                          p
 -}

  lemma-2-2-iii : {A B C : Set} → (f : A → B) → (g : B → C)
                 → {x y : A} → (p : x ≡ y)
                 → ap g (ap f p) ≡ ap (g ○ f) p
  lemma-2-2-iii f g refl = refl
  ap-hom-first = lemma-2-2-iii

 -- id : {A : Set} → A → A
 -- id x = x

 {-
  lemma-2-2-iv-0 : {A : Set} → {x : A} → ap id (refl' x) ≡ refl' x
  lemma-2-2-iv-0 = refl

  lemma-2-2-iv : {A : Set} → {x y : A} → (p : x ≡ y) → ap id p ≡ p
  lemma-2-2-iv p = j (λ x y p → ap id p ≡ p)
                     (λ x → lemma-2-2-iv-0)
                     p
 -}
  lemma-2-2-iv : {A : Set} → {x y : A} → (p : x ≡ y) → ap id p ≡ p
  lemma-2-2-iv refl = refl
  ap-id-first = lemma-2-2-iv
  apidp≡p = lemma-2-2-iv
