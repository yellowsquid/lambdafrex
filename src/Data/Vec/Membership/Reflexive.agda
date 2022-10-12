{-# OPTIONS --safe --without-K #-}

module Data.Vec.Membership.Reflexive where

open import Data.Fin
open import Data.Nat
open import Data.Product as ×
open import Data.Sum as ⊎
open import Data.Vec
open import Function using (_∘_)
open import Level using (Level)
open import Relation.Binary.PropositionalEquality
open import Relation.Nullary using (¬_)
open import Relation.Nullary.Negation using (contradiction)

private
  variable
    a : Level
    A : Set a
    x y : A
    m n : ℕ
    xs ys : Vec A n

-- Definition

infix 4 _∈_

data _∈_ {a} {A : Set a} (x : A) : Vec A n → Set a where
  here  : x ∈ x ∷ xs
  there : x ∈ xs → x ∈ y ∷ xs

-- Functions

index : x ∈ xs → Fin (length xs)
index here         = zero
index (there x∈xs) = suc (index x∈xs)

∈-lookup : ∀ i → lookup xs i ∈ xs
∈-lookup {xs = _ ∷ _} zero    = here
∈-lookup {xs = _ ∷ _} (suc i) = there (∈-lookup i)

∈-insert⁺ : x ∈ xs → ∀ i {y} → x ∈ insert xs i y
∈-insert⁺ x∈xs         zero    = there x∈xs
∈-insert⁺ here         (suc i) = here
∈-insert⁺ (there x∈xs) (suc i) = there (∈-insert⁺ x∈xs i)

remove-∈ : ∀ {xs : Vec A (suc n)} → x ∈ xs → Vec A n
remove-∈             {xs = x ∷ xs} here         = xs
remove-∈ {n = suc _} {xs = y ∷ xs} (there x∈xs) = y ∷ remove-∈ x∈xs

-- Properties

¬0⇒there : (y∈x∷xs : y ∈ x ∷ xs) → index y∈x∷xs ≢ zero → ∃ λ (y∈xs : y ∈ xs) → y∈x∷xs ≡ there y∈xs
¬0⇒there here         neq = contradiction refl neq
¬0⇒there (there y∈xs) neq = y∈xs , refl

remove-∈-≢ : ∀ {xs : Vec A (suc n)} →
  (x∈xs : x ∈ xs) (y∈xs : y ∈ xs) → index x∈xs ≢ index y∈xs → y ∈ remove-∈ x∈xs
remove-∈-≢             here         y∈xs         neq = ¬0⇒there y∈xs (neq ∘ sym) .proj₁
remove-∈-≢ {n = suc _} (there x∈xs) here         neq = here
remove-∈-≢ {n = suc _} (there x∈xs) (there y∈xs) neq = there (remove-∈-≢ x∈xs y∈xs (neq ∘ cong suc))
