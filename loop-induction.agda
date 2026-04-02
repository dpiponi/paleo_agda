 temp : {A : Set} (C : (x y : A) → x ≡ y → y ≡ x → Set) → (x₁ : A) (q₁ : x₁ ≡ x₁) → C x₁ x₁ refl q₁
 temp C x₁ q₁ = {!!} -- C x₁ x₁ refl q₁

 j₂' : {A : Set} (C : (x y : A) → x ≡ y → y ≡ x → Set)
      → ((x : A) → C x x refl refl)
      → {x y : A} → (p : x ≡ y) → (q : y ≡ x)
      → C x y p q
 j₂' {A} C f {x} {y} p q =
   j (λ x y p → (q : y ≡ x)
      → C x y p q)
      (temp C)
      p q

 j₁' : {A : Set} (C : (x : A) → x ≡ x → Set)
      → ((x : A) → C x refl)
      → {x : A} → (p : x ≡ x)
      → C x p
 j₁' C x refl = {!!}
