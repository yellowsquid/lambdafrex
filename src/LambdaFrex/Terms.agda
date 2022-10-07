{-# OPTIONS --safe --without-K #-}

open import Data.Product using (∃; _×_; _,_)
open import Relation.Binary.Indexed.Homogeneous

import LambdaFrex.Types as Types

module LambdaFrex.Terms
  {a} (G : Set a)
  (let open Types G)
  {b ℓ} (setoid : IndexedSetoid (∃ Context × Type) b ℓ)
  where

open import Data.Fin using (zero)
open import Data.Nat using (ℕ)
open import Data.Vec
open import Data.Vec.Membership.Reflexive
open import Level using (_⊔_)

open import LambdaFrex.Bundles G

private
  variable
    n : ℕ
    Γ Δ Ω : Context n
    A B : Type

  module M = IndexedSetoid setoid

  M : Context n → Type → Set b
  M Γ A = M.Carrierᵢ ((_ , Γ) , A)

infixl 5 _$_

data Term (Γ : Context n) : Type → Set (a ⊔ b) where
  meta  : (m : M Γ A) → Term Γ A
  subst : (σ : Subst Term Δ Γ) → Term Δ A → Term Γ A
  var   : (A∈Γ : A ∈ Γ) → Term Γ A
  ƛ     : Term (A ∷ Γ) B → Term Γ (A ⟶ B)
  _$_   : Term Γ (A ⟶ B) → Term Γ A → Term Γ B

ops : Ops Term
ops = record
  { subst = subst
  ; var = var
  ; ƛ = ƛ
  ; _$_ = _$_
  }

open Ops ops public using (weaken; wkn)

data _≈_ : IRel (λ (((n , Γ) , A) : ∃ Context × Type) → Term Γ A) (a ⊔ b ⊔ ℓ) where
  refl  : ∀ {t : Term Γ A} → t ≈ t
  sym   : ∀ {t t₁ : Term Γ A} → t ≈ t₁ → t₁ ≈ t
  trans : ∀ {t t₁ t₂ : Term Γ A} → t ≈ t₁ → t₁ ≈ t₂ → t ≈ t₂

  meta-cong  : ∀ {m m₁ : M Γ A} → m M.≈ᵢ m₁ → meta m ≈ meta m₁
  subst-cong : ∀ {γ δ : Subst Term Γ Δ} {t t₁ : Term Γ A} →
    (∀ {A} (A∈Γ : A ∈ Γ) → γ A∈Γ ≈ δ A∈Γ) → t ≈ t₁ →
    subst γ t ≈ subst δ t₁
  ƛ-cong     : ∀ {t t₁ : Term (A ∷ Γ) B} →
    t ≈ t₁ →
    ƛ t ≈ ƛ t₁
  $-cong     : ∀ {t t₂ : Term Γ (A ⟶ B)} {t₁ t₃ : Term Γ A} →
    t ≈ t₂ → t₁ ≈ t₃ →
    (t $ t₁) ≈ (t₂ $ t₃)

  subst-∘   : ∀ (γ : Subst Term Γ Δ) (δ : Subst Term Δ Ω) (t : Term Γ A) →
    subst δ (subst γ t) ≈ subst (λ A∈Γ → subst δ (γ A∈Γ)) t
  subst-var : ∀ (γ : Subst Term Γ Δ) (A∈Γ : A ∈ Γ) →
    subst γ (var A∈Γ) ≈ γ A∈Γ
  subst-ƛ   : ∀ (γ : Subst Term Γ Δ) (t : Term (A ∷ Γ) B) →
    subst γ (ƛ t) ≈ ƛ (subst (cons Term (var here) (wkn γ)) t)
  subst-$   : ∀ (γ : Subst Term Γ Δ) (t : Term Γ (A ⟶ B)) (t₁ : Term Γ A) →
    subst γ (t $ t₁) ≈ (subst γ t $ subst γ t₁)

  ⟶-β : ∀ (t : Term (A ∷ Γ) B) (t₁ : Term Γ A) → (ƛ t $ t₁) ≈ subst (cons Term t₁ var) t
  ⟶-η : ∀ (t : Term Γ (A ⟶ B)) → ƛ (weaken zero t $ var here) ≈ t

equality : Equality Term _≈_ ops
equality = record
  { isEquivalence = record { refl = refl ; sym = sym ; trans = trans }
  ; subst-cong = subst-cong
  ; ƛ-cong = ƛ-cong
  ; $-cong = $-cong
  ; subst-∘ = subst-∘
  ; subst-var = subst-var
  ; subst-ƛ = subst-ƛ
  ; subst-$ = subst-$
  ; ⟶-β = ⟶-β
  ; ⟶-η = ⟶-η
  }

open Equality equality public
  using (subst-congˡ; subst-congʳ; $-congˡ; $-congʳ)

algebra : LambdaAlgebra (a ⊔ b) (a ⊔ b ⊔ ℓ)
algebra = record { ops = ops ; equality = equality }
