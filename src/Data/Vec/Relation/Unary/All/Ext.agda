{-# OPTIONS --safe --without-K #-}

module Data.Vec.Relation.Unary.All.Ext where

open import Data.Fin using (zero; suc)
open import Data.Nat using (ℕ)
open import Data.Vec as Vec
open import Data.Vec.Membership.Reflexive
open import Data.Vec.Relation.Unary.All as All

open import Function using (_∘_; id)
open import Level using (Level)

open import Relation.Binary.PropositionalEquality using (_≡_; _≗_; refl; cong; cong₂)
open import Relation.Unary using (Pred; _⊆_)

private
  variable
    a p : Level
    A : Set a
    P Q R : Pred A p
    n : ℕ
    x y : A
    xs : Vec A n

lookup-∈ : All P xs → x ∈ xs → P x
lookup-∈ (px ∷ pxs) here         = px
lookup-∈ (px ∷ pxs) (there x∈xs) = lookup-∈ pxs x∈xs

∷-injectiveˡ : ∀ {px px₁ : P x} {pxs pxs₁ : All P xs} →
  _≡_ {A = All P (x ∷ xs)} (px ∷ pxs) (px₁ ∷ pxs₁) → px ≡ px₁
∷-injectiveˡ refl = refl

∷-injectiveʳ : ∀ {px px₁ : P x} {pxs pxs₁ : All P xs} →
  _≡_ {A = All P (x ∷ xs)} (px ∷ pxs) (px₁ ∷ pxs₁) → pxs ≡ pxs₁
∷-injectiveʳ refl = refl

-- Properties of map ----------------------------------------------------------

map-id : ∀ (pxs : All P xs) → All.map id pxs ≡ pxs
map-id []         = refl
map-id (px ∷ pxs) = cong₂ _∷_ refl (map-id pxs)

map-∘ : ∀ (f : Q ⊆ R) (g : P ⊆ Q) (pxs : All P xs) → All.map f (All.map g pxs) ≡ All.map (f ∘ g) pxs
map-∘ f g []         = refl
map-∘ f g (px ∷ pxs) = cong₂ _∷_ refl (map-∘ f g pxs)

map-cong : ∀ {f g : P ⊆ Q} → (∀ {x} → f {x} ≗ g) → All.map (λ {x} → f {x}) {x = xs} ≗ All.map g
map-cong f≗g []         = refl
map-cong f≗g (px ∷ pxs) = cong₂ _∷_ (f≗g px) (map-cong f≗g pxs)

lookup-∈-map : ∀ (f : P ⊆ Q) (pxs : All P xs) (x∈xs : x ∈ xs) →
  lookup-∈ (All.map f pxs) x∈xs ≡ f (lookup-∈ pxs x∈xs)
lookup-∈-map f (px ∷ pxs) here         = refl
lookup-∈-map f (px ∷ pxs) (there x∈xs) = lookup-∈-map f pxs x∈xs

-- Properties of tabulate -----------------------------------------------------

tabulate-∘ : ∀ {P : Pred A p} (f : P ⊆ Q) (g : ∀ i → P (Vec.lookup {n = n} xs i)) →
  All.map f {x = xs} (All.tabulate {P = P} g) ≡ All.tabulate (f ∘ g)
tabulate-∘ {xs = []}     f g = refl
tabulate-∘ {xs = x ∷ xs} f g = cong (f (g zero) ∷_) (tabulate-∘ f (g ∘ suc))
