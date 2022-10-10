{-# OPTIONS --safe --without-K #-}

module LambdaFrex.Bundles
  {a} (G : Set a)
  where

open import Data.Fin using (zero)
open import Data.Nat using (ℕ)
open import Data.Vec
open import Data.Vec.Membership.Reflexive
open import Data.Vec.Relation.Unary.All as All
open import Data.Vec.Relation.Unary.All.Ext as All
open import Data.Vec.Relation.Unary.All.Relation.Binary.Pointwise as Pointwise
open import Function using (Congruent; _∘_)
open import LambdaFrex.Types G
open import Level using (Level; _⊔_; suc)
open import Relation.Binary
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

private
  variable
    b c ℓ₁ ℓ₂ : Level
    m n : ℕ
    A B : Type
    Γ Δ Ω : Context n

module _ {b} (T : ∀ {n} → Context n → Type → Set b) where
  record Ops : Set (a ⊔ b) where
    infixl 5 _$_
    field
      subst : All (T Γ) Δ → T Δ A → T Γ A
      var   : A ∈ Γ → T Γ A
      ƛ     : T (A ∷ Γ) B → T Γ (A ⟶ B)
      _$_   : T Γ (A ⟶ B) → T Γ A → T Γ B

    weaken : ∀ i → T Γ A → T (insert Γ i B) A
    weaken i t = subst (All.tabulate (λ j → var (∈-insert⁺ (∈-lookup j) i))) t

    wkn : All (T Γ) Δ → All (T (A ∷ Γ)) Δ
    wkn γ = All.map (weaken zero) γ

  record Equality
    {ℓ} (_≈_ : ∀ {n} {Γ : Context n} {A} → Rel (T Γ A) ℓ) (ops : Ops)
    : Set (a ⊔ b ⊔ ℓ) where
    open Ops ops
    field
      isEquivalence : IsEquivalence (_≈_ {n} {Γ} {A})

    module ≈ {n} {Γ} {A} = IsEquivalence (isEquivalence {n} {Γ} {A})

    field
      subst-cong : ∀ {γ δ : All (T Γ) Δ} {t t₁ : T Δ A} →
        Pointwise _≈_ γ δ → t ≈ t₁ →
        subst γ t ≈ subst δ t₁
      ƛ-cong     : ∀ {t t₁ : T (A ∷ Γ) B} →
        t ≈ t₁ →
        ƛ t ≈ ƛ t₁
      $-cong     : ∀ {t t₂ : T Γ (A ⟶ B)} {t₁ t₃ : T Γ A} →
        t ≈ t₂ → t₁ ≈ t₃ →
        (t $ t₁) ≈ (t₂ $ t₃)

    field
      subst-∘   : ∀ (γ : All (T Γ) Δ) (δ : All (T Δ) Ω) (t : T Ω A) →
        subst γ (subst δ t) ≈ subst (All.map (subst γ) δ) t
      subst-var : ∀ (γ : All (T Δ) Γ) (A∈Γ : A ∈ Γ) →
        subst γ (var A∈Γ) ≈ lookup-∈ γ A∈Γ
      subst-ƛ   : ∀ (γ : All (T Δ) Γ) (t : T (A ∷ Γ) B) →
        subst γ (ƛ t) ≈ ƛ (subst (var here ∷ wkn γ) t)
      subst-$   : ∀ (γ : All (T Δ) Γ) (t : T Γ (A ⟶ B)) (t₁ : T Γ A) →
        subst γ (t $ t₁) ≈ (subst γ t $ subst γ t₁)

      ⟶-β : ∀ (t : T (A ∷ Γ) B) (t₁ : T Γ A) →
        (ƛ t $ t₁) ≈ subst (t₁ ∷ All.tabulate (var ∘ ∈-lookup)) t
      ⟶-η : ∀ (t : T Γ (A ⟶ B)) → ƛ (weaken zero t $ var here) ≈ t

    subst-congˡ : ∀ {γ δ : All (T Δ) Γ} {t : T Γ A} → Pointwise _≈_ γ δ → subst γ t ≈ subst δ t
    subst-congˡ γ≈δ = subst-cong γ≈δ ≈.refl

    subst-congʳ : ∀ {γ : All (T Δ) Γ} {t t₁ : T Γ A} → t ≈ t₁ → subst γ t ≈ subst γ t₁
    subst-congʳ t≈t₁ = subst-cong (Pointwise.refl ≈.refl) t≈t₁

    $-congˡ : ∀ {t t₁ : T Γ (A ⟶ B)} {t₂ : T Γ A} → t ≈ t₁ →
      (t $ t₂) ≈ (t₁ $ t₂)
    $-congˡ t≈t₁ = $-cong t≈t₁ ≈.refl

    $-congʳ : ∀ {t₂ : T Γ (A ⟶ B)} {t t₁ : T Γ A} → t ≈ t₁ →
      (t₂ $ t) ≈ (t₂ $ t₁)
    $-congʳ t≈t₁ = $-cong ≈.refl t≈t₁

record LambdaAlgebra b ℓ : Set (a ⊔ suc (b ⊔ ℓ)) where
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

    subst-homo : ∀ (γ : All (L.T Δ) Γ) (t : L.T Γ A) →
      ⟦ L.subst γ t ⟧ M.≈ M.subst (All.map ⟦_⟧ γ) ⟦ t ⟧
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
