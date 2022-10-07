{-# OPTIONS --safe --without-K #-}

module LambdaFrex.Category
  {a} (G : Set a) where

open import Categories.Category
open import Categories.Category.Helper
open import Categories.Category.Instance.IndexedSetoids
  renaming (_≃_ to _≃ᵢ_)
open import Categories.Functor
open import Data.Product using (∃; _×_; _,_)
import Function.Equality as F
open import Level
open import Relation.Binary.PropositionalEquality using (refl; setoid)

open import LambdaFrex.Bundles G
open import LambdaFrex.Types G

LambdaAlg : ∀ b ℓ → Category (a ⊔ suc b ⊔ suc ℓ) (a ⊔ b ⊔ ℓ) (a ⊔ b ⊔ ℓ)
LambdaAlg b ℓ = categoryHelper (record
  { Obj = LambdaAlgebra b ℓ
  ; _⇒_ = Lambda⇒
  ; _≈_ = _≃_
  ; id = λ {L} → let open LambdaAlgebra L in record
    { ⟦_⟧ = λ t → t
    ; cong = λ t≈t₁ → t≈t₁
    ; subst-homo = λ _ _ → ≈.refl
    ; var-homo = λ _ → ≈.refl
    ; ƛ-homo = λ _ → ≈.refl
    ; $-homo = λ _ _ → ≈.refl
    }
  ; _∘_ = λ {L M N} f g →
    let module N = LambdaAlgebra N in
    let module f = Lambda⇒ f in
    let module g = Lambda⇒ g in record
      { ⟦_⟧ = λ t → f.⟦ g.⟦ t ⟧ ⟧
      ; cong = λ t≈t₁ → f.cong (g.cong t≈t₁)
      ; subst-homo = λ γ t → N.≈.trans (f.cong (g.subst-homo γ t)) (f.subst-homo _ g.⟦ t ⟧)
      ; var-homo = λ A∈Γ → N.≈.trans (f.cong (g.var-homo A∈Γ)) (f.var-homo A∈Γ)
      ; ƛ-homo = λ t → N.≈.trans (f.cong (g.ƛ-homo t)) (f.ƛ-homo g.⟦ t ⟧)
      ; $-homo = λ t t₁ → N.≈.trans (f.cong (g.$-homo t t₁)) (f.$-homo g.⟦ t ⟧ g.⟦ t₁ ⟧)
      }
  ; assoc = λ {_ _ _ L} → let open LambdaAlgebra L in pw ≈.refl
  ; identityˡ = λ {_ L} → let open LambdaAlgebra L in pw ≈.refl
  ; identityʳ = λ {_ L} → let open LambdaAlgebra L in pw ≈.refl
  ; equiv = λ {_ L} → let open LambdaAlgebra L in record
    { refl = pw ≈.refl
    ; sym = λ f≃g → pw (≈.sym (f≃g .at))
    ; trans = λ f≃g g≃h → pw (≈.trans (f≃g .at) (g≃h .at))
    }
  ; ∘-resp-≈ = λ {_ _ L _ h} f≃h g≃i →
    let open LambdaAlgebra L in
    let module h = Lambda⇒ h in
    pw (≈.trans (f≃h .at) (h.cong (g≃i .at)))
  })

open LambdaAlgebra
open Lambda⇒

forget : ∀ {b ℓ} → Functor (LambdaAlg b ℓ) (IndexedSetoids (∃ Context × Type) b ℓ)
forget = record
  { F₀ = λ L → record
    { Carrierᵢ = λ ((n , Γ) , A) → L .T Γ A
    ; _≈ᵢ_ = L ._≈_
    ; isEquivalenceᵢ = record
      { reflᵢ = L .≈.refl
      ; symᵢ = L .≈.sym
      ; transᵢ = L .≈.trans
      }
    }
  ; F₁ = λ f → record
    { ⟦_⟧ = ⟦ f ⟧
    ; cong = f .cong
    }
  ; identity = λ {L} → pw (L .≈.refl)
  ; homomorphism = λ {_ _ L} → pw (L .≈.refl)
  ; F-resp-≈ = λ f≃g → pw (f≃g .at)
  }

module forget {b} {ℓ} = Functor (forget {b} {ℓ})
