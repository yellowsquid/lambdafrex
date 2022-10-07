{-# OPTIONS --safe --without-K #-}

module LambdaFrex.Bundles
  {a} (G : Set a)
  where

open import Data.Fin using (Fin)
open import Data.Nat hiding (_⊔_)
open import Data.Vec
open import Data.Vec.Membership.Reflexive
open import Function using (Congruent)
open import LambdaFrex.Types G
open import Level renaming (suc to lsuc)
open import Relation.Binary
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

private
  variable
    b c ℓ₁ ℓ₂ : Level
    m n : ℕ
    A B : Type
    Γ Δ Ω : Context n

module _ {b} (T : ∀ {n} → Context n → Type → Set b) where
  Subst : Context m → Context n → Set (a ⊔ b)
  Subst Γ Δ = ∀ {A} → A ∈ Γ → T Δ A

  cons : T Δ A → Subst Γ Δ → Subst (A ∷ Γ) Δ
  cons t γ here        = t
  cons t γ (there A∈Γ) = γ A∈Γ

  record Ops : Set (a ⊔ b) where
    infixl 5 _$_
    field
      subst : Subst Γ Δ → T Γ A → T Δ A
      var   : A ∈ Γ → T Γ A
      ƛ     : T (A ∷ Γ) B → T Γ (A ⟶ B)
      _$_   : T Γ (A ⟶ B) → T Γ A → T Γ B

    weaken : ∀ i → T Γ A → T (insert Γ i B) A
    weaken i t = subst (λ A∈Γ → var (∈-insert⁺ A∈Γ i)) t

    wkn : Subst Γ Δ → Subst Γ (A ∷ Δ)
    wkn γ A∈Γ = weaken Fin.zero (γ A∈Γ)

  record Equality
    {ℓ} (_≈_ : ∀ {n} {Γ : Context n} {A} → Rel (T Γ A) ℓ) (ops : Ops)
    : Set (a ⊔ b ⊔ ℓ) where
    open Ops ops
    field
      isEquivalence : IsEquivalence (_≈_ {n} {Γ} {A})

    module ≈ {n} {Γ} {A} = IsEquivalence (isEquivalence {n} {Γ} {A})

    field
      subst-cong : ∀ {γ δ : Subst Γ Δ} {t t₁ : T Γ A} →
        (∀ {A} (A∈Γ : A ∈ Γ) → γ A∈Γ ≈ δ A∈Γ) → t ≈ t₁ →
        subst γ t ≈ subst δ t₁
      ƛ-cong     : ∀ {t t₁ : T (A ∷ Γ) B} →
        t ≈ t₁ →
        ƛ t ≈ ƛ t₁
      $-cong     : ∀ {t t₂ : T Γ (A ⟶ B)} {t₁ t₃ : T Γ A} →
        t ≈ t₂ → t₁ ≈ t₃ →
        (t $ t₁) ≈ (t₂ $ t₃)

    field
      subst-∘   : ∀ (γ : Subst Γ Δ) (δ : Subst Δ Ω) (t : T Γ A) →
        subst δ (subst γ t) ≈ subst (λ A∈Γ → subst δ (γ A∈Γ)) t
      subst-var : ∀ (γ : Subst Γ Δ) (A∈Γ : A ∈ Γ) →
        subst γ (var A∈Γ) ≈ γ A∈Γ
      subst-ƛ   : ∀ (γ : Subst Γ Δ) (t : T (A ∷ Γ) B) →
        subst γ (ƛ t) ≈ ƛ (subst (cons (var here) (wkn γ)) t)
      subst-$   : ∀ (γ : Subst Γ Δ) (t : T Γ (A ⟶ B)) (t₁ : T Γ A) →
        subst γ (t $ t₁) ≈ (subst γ t $ subst γ t₁)

      ⟶-β : ∀ (t : T (A ∷ Γ) B) (t₁ : T Γ A) → (ƛ t $ t₁) ≈ subst (cons t₁ var) t
      ⟶-η : ∀ (t : T Γ (A ⟶ B)) → ƛ (weaken Fin.zero t $ var here) ≈ t

    subst-congˡ : ∀ {γ δ : Subst Γ Δ} {t : T Γ A} → (∀ {A} (A∈Γ : A ∈ Γ) → γ A∈Γ ≈ δ A∈Γ) →
      subst γ t ≈ subst δ t
    subst-congˡ γ≈δ = subst-cong γ≈δ ≈.refl

    subst-congʳ : ∀ {γ : Subst Γ Δ} {t t₁ : T Γ A} → t ≈ t₁ →
      subst γ t ≈ subst γ t₁
    subst-congʳ t≈t₁ = subst-cong (λ _ → ≈.refl) t≈t₁

    $-congˡ : ∀ {t t₁ : T Γ (A ⟶ B)} {t₂ : T Γ A} → t ≈ t₁ →
      (t $ t₂) ≈ (t₁ $ t₂)
    $-congˡ t≈t₁ = $-cong t≈t₁ ≈.refl

    $-congʳ : ∀ {t₂ : T Γ (A ⟶ B)} {t t₁ : T Γ A} → t ≈ t₁ →
      (t₂ $ t) ≈ (t₂ $ t₁)
    $-congʳ t≈t₁ = $-cong ≈.refl t≈t₁

record LambdaAlgebra b ℓ : Set (a ⊔ lsuc (b ⊔ ℓ)) where
  infix 4 _≈_
  field
    T   : Context n → Type → Set b
    _≈_ : Rel (T Γ A) ℓ

    ops : Ops T
    equality : Equality T _≈_ ops

  open Ops ops public
  open Equality equality public

record Lambda⇒ {b c ℓ₁ ℓ₂} (L : LambdaAlgebra b ℓ₁) (M : LambdaAlgebra c ℓ₂) : Set (a ⊔ b ⊔ c ⊔ ℓ₁ ⊔ ℓ₂) where
  private
    module L = LambdaAlgebra L
    module M = LambdaAlgebra M
  field
    ⟦_⟧  : L.T Γ A → M.T Γ A
    cong : Congruent L._≈_ M._≈_ (⟦_⟧ {n} {Γ} {A})

    subst-homo : ∀ (γ : Subst L.T Γ Δ) (t : L.T Γ A) →
      ⟦ L.subst γ t ⟧ M.≈ M.subst (λ A∈Γ → ⟦ γ A∈Γ ⟧) ⟦ t ⟧
    var-homo : ∀ (A∈Γ : A ∈ Γ) → ⟦ L.var A∈Γ ⟧ M.≈ M.var A∈Γ
    ƛ-homo : ∀ (t : L.T (A ∷ Γ) B) → ⟦ L.ƛ t ⟧ M.≈ M.ƛ ⟦ t ⟧
    $-homo : ∀ (t : L.T Γ (A ⟶ B)) (t₁ : L.T Γ A) → ⟦ t L.$ t₁ ⟧ M.≈ ⟦ t ⟧ M.$ ⟦ t₁ ⟧

infix 4 _≃_

record _≃_ {L : LambdaAlgebra b ℓ₁} {M : LambdaAlgebra c ℓ₂} (f g : Lambda⇒ L M) : Set (a ⊔ b ⊔ ℓ₂) where
  constructor pw
  private
    module f = Lambda⇒ f
    module g = Lambda⇒ g
    module L = LambdaAlgebra L
    module M = LambdaAlgebra M
  field
    at : ∀ {t : L.T Γ A} → f.⟦ t ⟧ M.≈ g.⟦ t ⟧

open _≃_ public
