{-# OPTIONS --safe --without-K #-}

module LambdaFrex.Types
  {a} (G : Set a)
  where

open import Data.Nat using (ℕ)
open import Data.Vec using (Vec)
open import Relation.Binary.PropositionalEquality

infixl 5 _⟶_

data Type : Set a where
  gnd : G → Type
  _⟶_ : Type → Type → Type

Context : ℕ → Set a
Context = Vec Type

⟶-injectiveˡ : ∀ {A B C D} → (A ⟶ B) ≡ (C ⟶ D) → A ≡ C
⟶-injectiveˡ refl = refl

⟶-injectiveʳ : ∀ {A B C D} → (A ⟶ B) ≡ (C ⟶ D) → B ≡ D
⟶-injectiveʳ refl = refl
