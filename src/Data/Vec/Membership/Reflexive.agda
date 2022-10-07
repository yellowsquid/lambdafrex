{-# OPTIONS --safe --without-K #-}

module Data.Vec.Membership.Reflexive where

open import Data.Fin
open import Data.Nat using (ℕ)
open import Data.Vec
open import Level using (Level)

private
  variable
    a : Level
    A : Set a
    x y z : A
    n : ℕ
    xs ys : Vec A n

infix 4 _∈_

data _∈_ {a} {A : Set a} (x : A) : Vec A n → Set a where
  here  : x ∈ x ∷ xs
  there : x ∈ xs → x ∈ y ∷ xs

∈-insert⁺ : x ∈ xs → ∀ i {y} → x ∈ insert xs i y
∈-insert⁺ x∈xs         zero    = there x∈xs
∈-insert⁺ here         (suc i) = here
∈-insert⁺ (there x∈xs) (suc i) = there (∈-insert⁺ x∈xs i)
