{-# OPTIONS --safe --without-K #-}

import LambdaFrex.Types as Types

module LambdaFrex.Terms.Properties
  {a} (G : Set a)
  (let open Types G)
  where

open import LambdaFrex.Bundles G
open import LambdaFrex.Category G
import LambdaFrex.Terms G as Terms renaming (_≈_ to ₍_₎_≈_)
import LambdaFrex.Terms.Morphism G as Morphs

open import Data.Nat using (ℕ)
open import Data.Product using (∃; _×_; _,_)
open import Data.Vec.Membership.Reflexive
open import Function as Fun using (_∘_)
open import Level using (_⊔_)
open import Relation.Binary.Indexed.Homogeneous

open import Categories.Adjoint using (_⊣_)
open import Categories.Category
open import Categories.Category.Instance.IndexedSetoids (∃ Context × Type) renaming (_≃_ to _≃ᵢ_)
open import Categories.Functor
open import Categories.NaturalTransformation

private
  variable
    n : ℕ
    Γ : Context n
    A : Type

free : ∀ {b ℓ} → Functor (IndexedSetoids b ℓ) (LambdaAlg (a ⊔ b) (a ⊔ b ⊔ ℓ))
free {b} {ℓ} = record
  { F₀ = Terms.algebra
  ; F₁ = Morphs.arr
  ; identity = pw (identity _)
  ; homomorphism = pw (homomorphism _)
  ; F-resp-≈ = λ f≃g → pw (resp-≈ f≃g _)
  }
  where
  identity :
    {S : IndexedSetoid (∃ Context × Type) b ℓ} →
    (t : Terms.Term S Γ A) →
    Terms.₍ S ₎ Morphs.⟦ Category.id (IndexedSetoids b ℓ) ⟧ t ≈ t
  identity (Terms.meta m)    = Terms.refl
  identity (Terms.subst σ t) = Terms.subst-cong (identity ∘ σ) (identity t)
  identity (Terms.var A∈Γ)   = Terms.refl
  identity (Terms.ƛ t)       = Terms.ƛ-cong (identity t)
  identity (t Terms.$ t₁)    = Terms.$-cong (identity t) (identity t₁)

  homomorphism :
    {S S₁ S₂ : IndexedSetoid (∃ Context × Type) b ℓ} →
    {f : Morphism S₁ S₂} {g : Morphism S S₁} →
    (t : Terms.Term S Γ A) →
    Terms.₍ S₂ ₎ Morphs.⟦ IndexedSetoids b ℓ [ f ∘ g ] ⟧ t ≈ Morphs.⟦ f ⟧ (Morphs.⟦ g ⟧ t)
  homomorphism (Terms.meta m)    = Terms.refl
  homomorphism (Terms.subst σ t) = Terms.subst-cong (homomorphism ∘ σ) (homomorphism t)
  homomorphism (Terms.var A∈Γ)   = Terms.refl
  homomorphism (Terms.ƛ t)       = Terms.ƛ-cong (homomorphism t)
  homomorphism (t Terms.$ t₁)    = Terms.$-cong (homomorphism t) (homomorphism t₁)

  resp-≈ :
    {S S₁ : IndexedSetoid (∃ Context × Type) b ℓ} {f g : Morphism S S₁} →
    f ≃ᵢ g → (t : Terms.Term S Γ A) →
    Terms.₍ S₁ ₎ Morphs.⟦ f ⟧ t ≈ Morphs.⟦ g ⟧ t
  resp-≈ f≃g (Terms.meta m)    = Terms.meta-cong (f≃g .at)
  resp-≈ f≃g (Terms.subst σ t) = Terms.subst-cong (resp-≈ f≃g ∘ σ) (resp-≈ f≃g t)
  resp-≈ f≃g (Terms.var A∈Γ)   = Terms.refl
  resp-≈ f≃g (Terms.ƛ t)       = Terms.ƛ-cong (resp-≈ f≃g t)
  resp-≈ f≃g (t Terms.$ t₁)    = Terms.$-cong (resp-≈ f≃g t) (resp-≈ f≃g t₁)

free⊣forget : ∀ {b ℓ} → free {a ⊔ b} {a ⊔ b ⊔ ℓ} ⊣ forget {a ⊔ b} {a ⊔ b ⊔ ℓ}
free⊣forget {b} {ℓ} = record
  { unit = ntHelper (record
    { η = unit
    ; commute = λ f → pw Terms.refl
    })
  ; counit = ntHelper (record
    { η = counit
    ; commute = λ f → pw (λ {_ _ _ t} → eval-commute f t)
    })
  ; zig = pw (zig _ _)
  ; zag = λ {A} → pw (LambdaAlgebra.≈.refl A)
  }
  where

  unit : ∀ X → Morphism X (forget.₀ (Terms.algebra X) )
  unit X = record { ⟦_⟧ = Terms.meta ; cong = Terms.meta-cong }

  module _ (X : LambdaAlgebra (a ⊔ b) (a ⊔ b ⊔ ℓ)) where
    open LambdaAlgebra X

    eval : Terms.Term (forget.₀ X) Γ A → T Γ A
    eval (Terms.meta m)    = m
    eval (Terms.subst σ t) = subst (eval ∘ σ) (eval t)
    eval (Terms.var A∈Γ)   = var A∈Γ
    eval (Terms.ƛ t)       = ƛ (eval t)
    eval (t Terms.$ t₁)    = eval t $ eval t₁

    eval-cong : ∀ {t t₁ : Terms.Term (forget.₀ X) Γ A} →
      Terms.₍ forget.₀ X ₎ t ≈ t₁ → eval t ≈ eval t₁
    eval-cong Terms.refl                  = ≈.refl
    eval-cong (Terms.sym t≈t₁)            = ≈.sym (eval-cong t≈t₁)
    eval-cong (Terms.trans t≈t₁ t≈t₂)     = ≈.trans (eval-cong t≈t₁) (eval-cong t≈t₂)
    eval-cong (Terms.meta-cong m≈m₁)      = m≈m₁
    eval-cong (Terms.subst-cong γ≈δ t≈t₁) = subst-cong (eval-cong ∘ γ≈δ) (eval-cong t≈t₁)
    eval-cong (Terms.ƛ-cong t≈t₁)         = ƛ-cong (eval-cong t≈t₁)
    eval-cong (Terms.$-cong t≈t₁ t≈t₂)    = $-cong (eval-cong t≈t₁) (eval-cong t≈t₂)
    eval-cong (Terms.subst-∘ γ δ t)       = subst-∘ (eval ∘ γ) (eval ∘ δ) (eval t)
    eval-cong (Terms.subst-var γ A∈Γ)     = subst-var (eval ∘ γ) A∈Γ
    eval-cong (Terms.subst-ƛ γ t)         = ≈.trans
      (subst-ƛ (eval ∘ γ) (eval t))
      (ƛ-cong (subst-congˡ λ
        { here        → ≈.refl
        ; (there A∈Γ) → ≈.refl
        }))
    eval-cong (Terms.subst-$ γ t t₁)      = subst-$ (eval ∘ γ) (eval t) (eval t₁)
    eval-cong (Terms.⟶-β t t₁)            = ≈.trans
      (⟶-β (eval t) (eval t₁))
      (subst-congˡ λ
        { here        → ≈.refl
        ; (there A∈Γ) → ≈.refl
        })
    eval-cong (Terms.⟶-η t)               = ⟶-η (eval t)

    counit : Lambda⇒ (Terms.algebra (forget.₀ X)) X
    counit = record
      { ⟦_⟧ = eval
      ; cong = eval-cong
      ; subst-homo = λ _ _ → ≈.refl
      ; var-homo = λ _ → ≈.refl
      ; ƛ-homo = λ _ → ≈.refl
      ; $-homo = λ _ _ → ≈.refl
      }

  module _ {X Y : LambdaAlgebra (a ⊔ b) (a ⊔ b ⊔ ℓ)} (f : Lambda⇒ X Y) where
    open Lambda⇒ f
    private
      module X = LambdaAlgebra X
      module Y = LambdaAlgebra Y

    eval-commute : ∀ (t : Terms.Term (forget.₀ X) Γ A) →
      eval Y (Morphs.⟦ forget.₁ f ⟧ t) Y.≈ ⟦ eval X t ⟧
    eval-commute (Terms.meta m)    = Y.≈.refl
    eval-commute (Terms.subst σ t) = Y.≈.trans
      (Y.subst-cong (eval-commute ∘ σ) (eval-commute t))
      (Y.≈.sym (subst-homo (eval X ∘ σ) (eval X t)))
    eval-commute (Terms.var A∈Γ)   = Y.≈.sym (var-homo A∈Γ)
    eval-commute (Terms.ƛ t)       = Y.≈.trans
      (Y.ƛ-cong (eval-commute t))
      (Y.≈.sym (ƛ-homo (eval X t)))
    eval-commute (t Terms.$ t₁)    = Y.≈.trans
      (Y.$-cong (eval-commute t) (eval-commute t₁))
      (Y.≈.sym ($-homo (eval X t) (eval X t₁)))

  module _ (S : IndexedSetoid (∃ Context × Type) (a ⊔ b) (a ⊔ b ⊔ ℓ)) where
    open IndexedSetoid S

    zig : (t : Terms.Term S Γ A) →
      Terms.₍ S ₎ eval (Functor.F₀ free S) (Morphs.⟦ unit S ⟧ t) ≈ t
    zig (Terms.meta m)    = Terms.refl
    zig (Terms.subst σ t) = Terms.subst-cong (zig ∘ σ) (zig t)
    zig (Terms.var A∈Γ)   = Terms.refl
    zig (Terms.ƛ t)       = Terms.ƛ-cong (zig t)
    zig (t Terms.$ t₁)    = Terms.$-cong (zig t) (zig t₁)
