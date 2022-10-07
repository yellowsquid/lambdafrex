{-# OPTIONS --safe --without-K #-}

open import Relation.Binary

module Categories.Category.Instance.IndexedSetoids
  {a} (I : Set a)
  where

open import Categories.Category
open import Function using (Congruent)
open import Level
open import Relation.Binary.Indexed.Homogeneous

record Morphism
  {b c ℓ₁ ℓ₂} (A : IndexedSetoid I b ℓ₁) (B : IndexedSetoid I c ℓ₂)
  : Set (a ⊔ b ⊔ c ⊔ ℓ₁ ⊔ ℓ₂) where
  private
    module A = IndexedSetoid A
    module B = IndexedSetoid B
  field
    ⟦_⟧  : ∀ {i} → A.Carrierᵢ i → B.Carrierᵢ i
    cong : ∀ {i} → Congruent A._≈ᵢ_ B._≈ᵢ_ (⟦_⟧ {i})

record _≃_
  {b c ℓ₁ ℓ₂} {A : IndexedSetoid I b ℓ₁} {B : IndexedSetoid I c ℓ₂} (f g : Morphism A B)
  : Set (a ⊔ b ⊔ ℓ₂) where
  constructor pw
  private
    module B = IndexedSetoid B
    module f = Morphism f
    module g = Morphism g
  field
    at : ∀ {i x} → f.⟦_⟧ {i} x B.≈ᵢ g.⟦ x ⟧

open _≃_ public

IndexedSetoids : ∀ b ℓ → Category (suc (a ⊔ b ⊔ ℓ)) (a ⊔ b ⊔ ℓ) (a ⊔ b ⊔ ℓ)
IndexedSetoids b ℓ = record
  { Obj = IndexedSetoid I b ℓ
  ; _⇒_ = Morphism
  ; _≈_ = _≃_
  ; id = record { ⟦_⟧ = λ x → x ; cong = λ x≈y → x≈y }
  ; _∘_ = λ f g →
    let module f = Morphism f in
    let module g = Morphism g in record
      { ⟦_⟧ = λ x → f.⟦ g.⟦ x ⟧ ⟧
      ; cong = λ x≈y → f.cong (g.cong x≈y)
      }
  ; assoc = λ {_ _ _ D} → let open IndexedSetoid D in pw reflᵢ
  ; sym-assoc = λ {_ _ _ D} → let open IndexedSetoid D in pw reflᵢ
  ; identityˡ = λ {_ B} → let open IndexedSetoid B in pw reflᵢ
  ; identityʳ = λ {_ B} → let open IndexedSetoid B in pw reflᵢ
  ; identity² = λ {A} → let open IndexedSetoid A in pw reflᵢ
  ; equiv = λ {_ B} → let open IndexedSetoid B in record
    { refl = pw reflᵢ
    ; sym = λ f≃g → pw (symᵢ (f≃g .at))
    ; trans = λ f≃g g≃h → pw (transᵢ (f≃g .at) (g≃h .at))
    }
  ; ∘-resp-≈ = λ {_ _ C f} f≃h g≃i →
    let open IndexedSetoid C in
    let module f = Morphism f in
    pw (transᵢ (f.cong (g≃i .at)) (f≃h .at))
  }
