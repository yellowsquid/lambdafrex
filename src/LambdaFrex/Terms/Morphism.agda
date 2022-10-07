{-# OPTIONS --safe --without-K #-}

open import Categories.Category.Instance.IndexedSetoids
open import Data.Product using (∃; _×_; _,_)
open import Relation.Binary.Indexed.Homogeneous

import LambdaFrex.Types as Types

module LambdaFrex.Terms.Morphism
  {a} (G : Set a)
  (let open Types G)
  {b ℓ₁} {from : IndexedSetoid (∃ Context × Type) b ℓ₁}
  {c ℓ₂} {to : IndexedSetoid (∃ Context × Type) c ℓ₂}
  (f : Morphism (∃ Context × Type) from to)
  where

open import Data.Nat using (ℕ)
open import Data.Vec.Membership.Reflexive
open import Function using (Congruent; _∘_)

open import LambdaFrex.Bundles G
import LambdaFrex.Terms G as Terms

private
  variable
    n : ℕ
    Γ : Context n
    A B : Type

  module f = Morphism f
  module from = Terms from
  module to = Terms to

⟦_⟧ : from.Term Γ A → to.Term Γ A
⟦ from.meta m ⟧    = to.meta f.⟦ m ⟧
⟦ from.subst σ t ⟧ = to.subst (⟦_⟧ ∘ σ) ⟦ t ⟧
⟦ from.var A∈Γ ⟧   = to.var A∈Γ
⟦ from.ƛ t ⟧       = to.ƛ ⟦ t ⟧
⟦ t from.$ t₁ ⟧    = ⟦ t ⟧ to.$ ⟦ t₁ ⟧

cong : Congruent from._≈_ to._≈_ (⟦_⟧ {n} {Γ} {A})
cong from.refl                  = to.refl
cong (from.sym t≈t₁)            = to.sym (cong t≈t₁)
cong (from.trans t≈t₁ t₁≈t₂)    = to.trans (cong t≈t₁) (cong t₁≈t₂)
cong (from.meta-cong m≈m₁)      = to.meta-cong (f.cong m≈m₁)
cong (from.subst-cong γ≈δ t≈t₁) = to.subst-cong (λ A∈Γ → cong (γ≈δ A∈Γ)) (cong t≈t₁)
cong (from.ƛ-cong t≈t₁)         = to.ƛ-cong (cong t≈t₁)
cong (from.$-cong t≈t₂ t₁≈t₃)   = to.$-cong (cong t≈t₂) (cong t₁≈t₃)
cong (from.subst-∘ γ δ t)       = to.subst-∘ (⟦_⟧ ∘ γ) (⟦_⟧ ∘ δ) ⟦ t ⟧
cong (from.subst-var γ A∈Γ)     = to.subst-var (⟦_⟧ ∘ γ) A∈Γ
cong (from.subst-ƛ γ t)         = to.trans
  (to.subst-ƛ (⟦_⟧ ∘ γ) ⟦ t ⟧)
  (to.ƛ-cong (to.subst-congˡ (λ
    { here        → to.refl
    ; (there A∈Γ) → to.refl
    })))
cong (from.subst-$ γ t t₁)      = to.subst-$ (⟦_⟧ ∘ γ) ⟦ t ⟧ ⟦ t₁ ⟧
cong (from.⟶-β t t₁)            = to.trans
  (to.⟶-β ⟦ t ⟧ ⟦ t₁ ⟧)
  (to.subst-congˡ (λ
    { here        → to.refl
    ; (there A∈Γ) → to.refl
    }))
cong (from.⟶-η t)               = to.⟶-η ⟦ t ⟧

arr : Lambda⇒ from.algebra to.algebra
arr = record
  { ⟦_⟧ = ⟦_⟧
  ; cong = cong
  ; subst-homo = λ _ _ → to.refl
  ; var-homo = λ _ → to.refl
  ; ƛ-homo = λ _ → to.refl
  ; $-homo = λ _ _ → to.refl
  }
