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

open import Data.Fin using (zero; suc)
open import Data.Nat using (ℕ)
open import Data.Vec.Membership.Reflexive
open import Data.Vec.Relation.Unary.All
open import Data.Vec.Relation.Unary.All.Ext
open import Data.Vec.Relation.Unary.All.Relation.Binary.Pointwise as Pw

open import Function using (Congruent; _∘_)

open import Relation.Binary.PropositionalEquality as ≡ using (_≡_; module ≡-Reasoning)

open import LambdaFrex.Bundles G
import LambdaFrex.Terms G as Terms

open ≡-Reasoning

private
  variable
    m n : ℕ
    Γ Δ : Context n
    A B : Type

  module f = Morphism f
  module from = Terms from
  module to = Terms to

⟦_⟧ : from.Term Γ A → to.Term Γ A
⟦_⟧* : All (from.Term Γ) Δ → All (to.Term Γ) Δ

⟦ from.meta m ⟧    = to.meta (f.⟦ m ⟧)
⟦ from.subst σ t ⟧ = to.subst ⟦ σ ⟧* ⟦ t ⟧
⟦ from.var A∈Γ ⟧   = to.Term.var A∈Γ
⟦ from.ƛ t ⟧       = to.ƛ ⟦ t ⟧
⟦ t from.$ t₁ ⟧    = ⟦ t ⟧ to.$ ⟦ t₁ ⟧

⟦ [] ⟧*    = []
⟦ t ∷ σ ⟧* = ⟦ t ⟧ ∷ ⟦ σ ⟧*

⟦σ⟧*≡map⟦-⟧ : (σ : All (from.Term Γ) Δ) → ⟦ σ ⟧* ≡ map ⟦_⟧ σ
⟦σ⟧*≡map⟦-⟧ []      = ≡.refl
⟦σ⟧*≡map⟦-⟧ (t ∷ σ) = ≡.cong (⟦ t ⟧ ∷_) (⟦σ⟧*≡map⟦-⟧ σ)

cong : Congruent from._≈_ to._≈_ (⟦_⟧ {n} {Γ} {A})
cong* : Congruent (Pointwise from._≈_) (Pointwise to._≈_) (⟦_⟧* {m} {Γ} {n} {Δ})

cong from.refl                  = to.refl
cong (from.sym t≈t₁)            = to.sym (cong t≈t₁)
cong (from.trans t≈t₁ t₁≈t₂)    = to.trans (cong t≈t₁) (cong t₁≈t₂)
cong (from.meta-cong m≈m₁)      = to.meta-cong (f.cong m≈m₁)
cong (from.subst-cong γ≈δ t≈t₁) = to.subst-cong (cong* γ≈δ) (cong t≈t₁)
cong (from.ƛ-cong t≈t₁)         = to.ƛ-cong (cong t≈t₁)
cong (from.$-cong t≈t₂ t₁≈t₃)   = to.$-cong (cong t≈t₂) (cong t₁≈t₃)
cong (from.subst-∘ γ δ t)       = to.trans
  (to.subst-∘ ⟦ γ ⟧* ⟦ δ ⟧* ⟦ t ⟧)
  (to.subst-congˡ (reflexive to.≈.reflexive (≡⇒Pointwise≡ (begin
    map (to.subst ⟦ γ ⟧*) ⟦ δ ⟧*      ≡⟨  ≡.cong (map _) (⟦σ⟧*≡map⟦-⟧ δ) ⟩
    map (to.subst ⟦ γ ⟧*) (map ⟦_⟧ δ) ≡⟨  map-∘ (to.subst ⟦ γ ⟧*) ⟦_⟧ δ ⟩
    map (to.subst ⟦ γ ⟧* ∘ ⟦_⟧) δ     ≡⟨⟩
    map (⟦_⟧ ∘ from.subst γ) δ       ≡˘⟨ map-∘ ⟦_⟧ (from.subst γ) δ ⟩
    map ⟦_⟧ (map (from.subst γ) δ)   ≡˘⟨ ⟦σ⟧*≡map⟦-⟧ (map (from.subst γ) δ) ⟩
    ⟦ map (from.subst γ) δ ⟧*        ∎))))
cong (from.subst-var γ A∈Γ)     = to.trans
  (to.subst-var ⟦ γ ⟧* A∈Γ)
  (to.≈.reflexive (begin
    lookup-∈ ⟦ γ ⟧* A∈Γ      ≡⟨ ≡.cong (λ γ → lookup-∈ γ A∈Γ) (⟦σ⟧*≡map⟦-⟧ γ) ⟩
    lookup-∈ (map ⟦_⟧ γ) A∈Γ ≡⟨ lookup-∈-map ⟦_⟧ γ A∈Γ ⟩
    ⟦ lookup-∈ γ A∈Γ ⟧       ∎))
cong (from.subst-ƛ γ t)         = to.trans
  (to.subst-ƛ ⟦ γ ⟧* ⟦ t ⟧)
  (to.ƛ-cong (to.subst-congˡ (to.refl ∷ reflexive to.≈.reflexive (≡⇒Pointwise≡ (begin
    to.wkn ⟦ γ ⟧*                      ≡⟨⟩
    map (to.weaken zero) ⟦ γ ⟧*        ≡⟨  ≡.cong (map _) (⟦σ⟧*≡map⟦-⟧ γ) ⟩
    map (to.weaken zero) (map ⟦_⟧ γ)   ≡⟨  map-∘ (to.weaken zero) ⟦_⟧ γ ⟩
    map (to.weaken zero ∘ ⟦_⟧) γ       ≡⟨  map-cong (λ t → ≡.cong (λ σ → to.subst σ ⟦ t ⟧) (begin
      tabulate (to.var ∘ ∈-lookup ∘ suc)             ≡⟨⟩
      tabulate (⟦_⟧ ∘ from.var ∘ ∈-lookup ∘ suc)     ≡˘⟨ tabulate-∘ ⟦_⟧ (from.var ∘ ∈-lookup ∘ suc) ⟩
      map ⟦_⟧ (tabulate (from.var ∘ ∈-lookup ∘ suc)) ≡˘⟨ ⟦σ⟧*≡map⟦-⟧ (tabulate (from.var ∘ ∈-lookup ∘ suc)) ⟩
      ⟦ tabulate (from.var ∘ ∈-lookup ∘ suc) ⟧*      ∎)) γ ⟩
    map (⟦_⟧ ∘ from.weaken zero) γ     ≡˘⟨ map-∘ ⟦_⟧ (from.weaken zero) γ ⟩
    map ⟦_⟧ (map (from.weaken zero) γ) ≡⟨⟩
    map ⟦_⟧ (from.wkn γ)               ≡˘⟨ ⟦σ⟧*≡map⟦-⟧ (from.wkn γ) ⟩
    ⟦ from.wkn γ ⟧*                    ∎)))))
cong (from.subst-$ γ t t₁)      = to.subst-$ ⟦ γ ⟧* ⟦ t ⟧ ⟦ t₁ ⟧
cong (from.⟶-β t t₁)            = to.trans
  (to.⟶-β ⟦ t ⟧ ⟦ t₁ ⟧)
  (to.subst-congˡ (to.refl ∷ reflexive to.≈.reflexive (≡⇒Pointwise≡ (begin
    tabulate (to.var ∘ ∈-lookup)             ≡⟨⟩
    tabulate (⟦_⟧ ∘ from.var ∘ ∈-lookup)     ≡˘⟨ tabulate-∘ ⟦_⟧ (from.var ∘ ∈-lookup) ⟩
    map ⟦_⟧ (tabulate (from.var ∘ ∈-lookup)) ≡˘⟨ ⟦σ⟧*≡map⟦-⟧ (tabulate (from.var ∘ ∈-lookup)) ⟩
    ⟦ tabulate (from.var ∘ ∈-lookup) ⟧*      ∎))))
cong (from.⟶-η t)               = to.trans
  (to.ƛ-cong (to.$-congˡ (to.subst-congˡ (reflexive to.≈.reflexive (≡⇒Pointwise≡ (begin
    ⟦ tabulate (from.var ∘ ∈-lookup ∘ suc) ⟧*      ≡⟨ ⟦σ⟧*≡map⟦-⟧ (tabulate (from.var ∘ ∈-lookup ∘ suc)) ⟩
    map ⟦_⟧ (tabulate (from.var ∘ ∈-lookup ∘ suc)) ≡⟨ tabulate-∘ ⟦_⟧ (from.var ∘ ∈-lookup ∘ suc) ⟩
    tabulate (⟦_⟧ ∘ from.var ∘ ∈-lookup ∘ suc)     ≡⟨⟩
    tabulate (to.var ∘ ∈-lookup ∘ suc)             ∎))))))
  (to.⟶-η ⟦ t ⟧)

cong* []           = []
cong* (t≈t₁ ∷ γ≈δ) = cong t≈t₁ ∷ cong* γ≈δ

arr : Lambda⇒ from.algebra to.algebra
arr = record
  { ⟦_⟧ = ⟦_⟧
  ; cong = cong
  ; subst-homo = λ γ _ → to.subst-congˡ (reflexive to.≈.reflexive (≡⇒Pointwise≡ (⟦σ⟧*≡map⟦-⟧ γ)))
  ; var-homo = λ _ → to.refl
  ; ƛ-homo = λ _ → to.refl
  ; $-homo = λ _ _ → to.refl
  }
