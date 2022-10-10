{-# OPTIONS --safe --without-K #-}

module Data.Vec.Relation.Unary.All.Relation.Binary.Pointwise where

open import Data.Nat using (ℕ)
open import Data.Vec
open import Data.Vec.Relation.Unary.All
open import Data.Vec.Relation.Unary.All.Ext

open import Level using (Level; _⊔_)

open import Relation.Binary using (REL; Reflexive; _⇒_)
open import Relation.Binary.Indexed.Homogeneous
  using (IREL; IRel; Implies)
  renaming (Reflexive to Reflexiveᵢ)
open import Relation.Binary.PropositionalEquality as ≡ using (_≡_)
open import Relation.Unary using (Pred)

private
  variable
    a p r s : Level
    A : Set a
    n : ℕ
    xs : Vec A n

infixr 5 _∷_

data Pointwise {a p q r} {A : Set a} {P : Pred A p} {Q : Pred A q} (R : IREL P Q r)
  : ∀ {n} {xs : Vec A n} → REL (All P xs) (All Q xs) (a ⊔ p ⊔ q ⊔ r) where
  []  : Pointwise R [] []
  _∷_ : ∀ {n x px qx xs pxs qxs} →
    (rx : R {x} px qx) → Pointwise R {n} {xs} pxs qxs → Pointwise R (px ∷ pxs) (qx ∷ qxs)

refl : ∀ {P : Pred A p} {R : IRel P r} →
  Reflexiveᵢ P R → Reflexive (Pointwise (λ {x} → R {x}) {n} {xs})
refl reflᵢ {[]}       = []
refl reflᵢ {px ∷ pxs} = reflᵢ ∷ refl reflᵢ

reflexive : ∀ {P : Pred A p} {R : IRel P r} {S : IRel P s} →
  R ⇒[ P ] S → Pointwise (λ {x} → R {x}) {n} {xs} ⇒ Pointwise S
reflexive R⇒S []         = []
reflexive R⇒S (rx ∷ rxs) = R⇒S rx ∷ reflexive R⇒S rxs

≡⇒Pointwise≡ : ∀ {P : Pred A p} → _≡_ ⇒ Pointwise {P = P} _≡_ {n} {xs}
≡⇒Pointwise≡ {x = []}       {[]}    eq = []
≡⇒Pointwise≡ {x = px ∷ pxs} {_ ∷ _} eq = ∷-injectiveˡ eq ∷ ≡⇒Pointwise≡ (∷-injectiveʳ eq)
