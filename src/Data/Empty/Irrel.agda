{-# OPTIONS --safe --without-K #-}

module Data.Empty.Irrel where

open import Data.Bool using (not)
open import Data.Empty using () renaming (⊥ to Empty)
open import Relation.Nullary using (Dec; ofʸ; ofⁿ; does; proof; yes; no)
open import Relation.Nullary.Reflects

record ⊥ : Set where
  field
    .empty : Empty

¬_ : ∀ {a} → Set a → Set a
¬ A = A → ⊥

contradiction : ∀ {a b} {A : Set a} {B : Set b} → A → ¬ A → B
contradiction a ¬a with () ← ¬a a

mkRel : ∀ {a} {A : Set a} → ¬ A → A → Empty
mkRel ¬a a = contradiction a ¬a

mkIrrel : ∀ {a} {A : Set a} → (A → Empty) → ¬ A
mkIrrel ¬a a = record { empty = ¬a a }

¬? : ∀ {a} {A : Set a} → Dec A → Dec (¬ A)
does  (¬? p?)      = not (does p?)
proof (¬? (yes p)) = ofⁿ (contradiction p)
proof (¬? (no ¬p)) = ofʸ (mkIrrel ¬p)
