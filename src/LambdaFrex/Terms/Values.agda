{-# OPTIONS --safe --without-K #-}

open import Data.Product
open import Relation.Binary.Indexed.Homogeneous using (IndexedSetoid)

import LambdaFrex.Types as Types

module LambdaFrex.Terms.Values
  {a} (G : Set a)
  (let open Types G)
  {b ℓ} (setoid : IndexedSetoid (∃ Context × Type) b ℓ)
  where

open import Data.Empty.Irrel
open import Data.Fin using (_≟_)
open import Data.Nat using (ℕ)
open import Data.Sum using (inj₁; inj₂; [_,_]′)
open import Data.Vec
open import Data.Vec.Membership.Reflexive
open import Data.Vec.Relation.Unary.All
open import Data.Vec.Relation.Unary.All.Ext

open import Function using (_∘_)
open import Level using (_⊔_)

open import Relation.Binary.PropositionalEquality as ≡ using (_≡_)
open import Relation.Nullary using (yes; no)
open import Relation.Nullary.Decidable using (map′)
open import Relation.Nullary.Product using (_×-dec_)
open import Relation.Nullary.Sum using (_⊎-dec_)
open import Relation.Unary using (Decidable)

open import LambdaFrex.Bundles G
open import LambdaFrex.Terms G setoid

private
  variable
    m n : ℕ
    Γ Δ Δ′ Ω : Context n
    A B C : Type

  module M = IndexedSetoid setoid

  M : Context n → Type → Set b
  M Γ A = M.Carrierᵢ ((_ , Γ) , A)

-- Occurs check --------------------------------------------------------------

-- Definition

data Occurs (A∈Γ : A ∈ Γ) : Term Γ B → Set (a ⊔ b)
data Occurs* (A∈Γ : A ∈ Γ) : All (Term Γ) Δ → Set (a ⊔ b)

data Occurs {A} {_} {Γ} A∈Γ where
  meta : (m : M Γ B) → Occurs A∈Γ (meta m)
  subst : ∀ {σ : All (Term Γ) Δ} → Occurs* A∈Γ σ → (t : Term Δ C) → Occurs A∈Γ (subst σ t)
  var : ∀ {B∈Γ : B ∈ Γ} → index A∈Γ ≡ index B∈Γ → Occurs A∈Γ (var B∈Γ)
  ƛ   : {t : Term (B ∷ Γ) C} → Occurs (there A∈Γ) t → Occurs A∈Γ (ƛ t)
  $ₗ   : ∀ {t : Term Γ (B ⟶ C)} {t₁ : Term Γ B} → Occurs A∈Γ t → Occurs A∈Γ (t $ t₁)
  $ᵣ   : ∀ {t : Term Γ (B ⟶ C)} {t₁ : Term Γ B} → Occurs A∈Γ t₁ → Occurs A∈Γ (t $ t₁)

data Occurs* {A} {_} {Γ} A∈Γ where
  here  : ∀ {t : Term Γ B} {σ : All (Term Γ) Δ} → Occurs A∈Γ t  → Occurs* A∈Γ (t ∷ σ)
  there : ∀ {t : Term Γ B} {σ : All (Term Γ) Δ} → Occurs* A∈Γ σ → Occurs* A∈Γ (t ∷ σ)

-- Decidability

Occurs? : ∀ (A∈Γ : A ∈ Γ) → Decidable (Occurs A∈Γ {B})
Occurs*? : ∀ (A∈Γ : A ∈ Γ) → Decidable (Occurs* A∈Γ {Δ = Δ})

Occurs? A∈Γ (meta m)    = yes (meta m)
Occurs? A∈Γ (subst σ t) = map′ (λ σ → subst σ t) (λ { (subst σ t) → σ }) (Occurs*? A∈Γ σ)
Occurs? A∈Γ (var B∈Γ)   = map′ var (λ { (var eq) → eq }) (index A∈Γ ≟ index B∈Γ)
Occurs? A∈Γ (ƛ t)       = map′ ƛ (λ { (ƛ occurs) → occurs }) (Occurs? (there A∈Γ) t)
Occurs? A∈Γ (t $ t₁)    = map′
  [ $ₗ , $ᵣ ]′
  (λ { ($ₗ occurs) → inj₁ occurs ; ($ᵣ occurs) → inj₂ occurs })
  (Occurs? A∈Γ t ⊎-dec Occurs? A∈Γ t₁)

Occurs*? A∈Γ []      = no λ ()
Occurs*? A∈Γ (t ∷ σ) = map′
  [ here , there ]′
  (λ { (here occurs) → inj₁ occurs ; (there occurs) → inj₂ occurs})
  (Occurs? A∈Γ t ⊎-dec Occurs*? A∈Γ σ)

-- Eta Reducibility -----------------------------------------------------------

data IsEtaReducible : Term Γ B → Set (a ⊔ b) where
  here  : ∀ {t : Term (A ∷ Γ) (A ⟶ B)} → ¬ Occurs here t → IsEtaReducible (t $ var here)

-- Decidability

IsEtaReducible? : Decidable (IsEtaReducible {Γ = Γ} {A})
IsEtaReducible? (meta m)              = no λ ()
IsEtaReducible? (subst σ t)           = no λ ()
IsEtaReducible? (var B∈Γ)             = no λ ()
IsEtaReducible? (ƛ t)                 = no λ ()
IsEtaReducible? (t $ meta m)          = no λ ()
IsEtaReducible? (t $ subst σ t₁)      = no λ ()
IsEtaReducible? (t $ var here)        = map′
  here
  (λ { (here ¬occurs) → ¬occurs })
  (¬? (Occurs? here t))
IsEtaReducible? (t $ var (there A∈Γ)) = no λ ()
IsEtaReducible? (t $ ƛ t₁)            = no λ ()
IsEtaReducible? (t $ (t₁ $ t₂))       = no λ ()

-- Values ---------------------------------------------------------------------

-- Definition

infixr 5 _∷_

data IsRoot : Term Γ A → Set (a ⊔ b)
data IsApp : Term Γ A → Set (a ⊔ b)
data IsValue : Term Γ A → Set (a ⊔ b)
data AllValues : All (Term Γ) Δ → Set (a ⊔ b)

data IsRoot where
  meta′ : ∀ (m : M Γ A) → IsRoot (meta m)
  meta  :
    ∀ {σ : All (Term Γ) Δ} →
    AllValues σ → (m : M Δ A) →
    IsRoot (subst σ (meta m))
  var   : ∀ (A∈Γ : A ∈ Γ) → IsRoot (var A∈Γ)

data IsApp where
  root : ∀ {t : Term Γ A} → IsRoot t → IsApp t
  _$_  : ∀ {t : Term Γ (A ⟶ B)} {t₁ : Term Γ A} → IsApp t → IsValue t₁ → IsApp (t $ t₁)

data IsValue where
  app : ∀ {t : Term Γ A} → IsApp t → IsValue t
  ƛ   : ∀ {t : Term (A ∷ Γ) B} → IsValue t → ¬ IsEtaReducible t → IsValue (ƛ t)

data AllValues where
  []  : AllValues {Γ = Γ} []
  _∷_ : ∀ {t : Term Γ A} {σ : All (Term Γ) Δ} →
    (t-val : IsValue t) → AllValues σ → AllValues (t ∷ σ)

-- Decidability

IsRoot?    : Decidable (IsRoot {Γ = Γ} {A})
IsApp?     : Decidable (IsApp {Γ = Γ} {A})
IsValue?   : Decidable (IsValue {Γ = Γ} {A})
AllValues? : Decidable (AllValues {Γ = Γ} {Δ = Δ})

IsRoot? (meta m)               = yes (meta′ m)
IsRoot? (subst σ (meta m))     = map′ (λ σ → meta σ m) (λ { (meta σ m) → σ }) (AllValues? σ)
IsRoot? (subst σ (subst σ₁ t)) = no λ ()
IsRoot? (subst σ (var A∈Γ))    = no λ ()
IsRoot? (subst σ (ƛ t))        = no λ ()
IsRoot? (subst σ (t $ t₁))     = no λ ()
IsRoot? (var A∈Γ)              = yes (var A∈Γ)
IsRoot? (ƛ t)                  = no λ ()
IsRoot? (t $ t₁)               = no λ ()

IsApp? (t $ t₁)      = map′ (uncurry _$_) (λ { (t $ t₁) → t , t₁ }) (IsApp? t ×-dec IsValue? t₁)
IsApp? (meta m)      = yes (root (meta′ m))
IsApp? t@(subst _ _) = map′ root (λ { (root t) → t }) (IsRoot? t)
IsApp? (var A∈Γ)     = yes (root (var A∈Γ))
IsApp? (ƛ t)         = no λ { (root ()) }

IsValue? (meta m)      = yes (app (root (meta′ m)))
IsValue? t@(subst _ _) = map′ app (λ { (app t) → t }) (IsApp? t)
IsValue? (var A∈Γ)     = yes (app (root (var A∈Γ)))
IsValue? (ƛ t)         = map′
  (uncurry ƛ)
  (λ { (ƛ t ¬η) → t , ¬η ; (app (root ())) })
  (IsValue? t ×-dec ¬? (IsEtaReducible? t))
IsValue? t@(_ $ _)     = map′ app (λ { (app t) → t }) (IsApp? t)

AllValues? []      = yes []
AllValues? (t ∷ σ) = map′ (uncurry _∷_) (λ { (t ∷ σ) → t , σ }) (IsValue? t ×-dec AllValues? σ)

-- Strengthening terms --------------------------------------------------------

-- Definition

strengthen : (A∈Γ : A ∈ Γ) → (t : Term Γ B) → ¬ Occurs A∈Γ t → Term (remove-∈ A∈Γ) B
strengthen* : (A∈Γ : A ∈ Γ) → (σ : All (Term Γ) Δ) → ¬ Occurs* A∈Γ σ → All (Term (remove-∈ A∈Γ)) Δ

strengthen A∈Γ (meta m)    ¬occurs = contradiction (meta m) ¬occurs
strengthen A∈Γ (subst σ t) ¬occurs = subst
  (strengthen* A∈Γ σ λ occurs* → ¬occurs (subst occurs* t))
  t
strengthen A∈Γ (var B∈Γ)   ¬occurs = var (remove-∈-≢ A∈Γ B∈Γ (mkRel (¬occurs ∘ var)))
strengthen A∈Γ (ƛ t)       ¬occurs = ƛ (strengthen (there A∈Γ) t (¬occurs ∘ ƛ))
strengthen A∈Γ (t $ t₁)    ¬occurs =
  strengthen A∈Γ t (¬occurs ∘ $ₗ) $
  strengthen A∈Γ t₁ (¬occurs ∘ $ᵣ)

strengthen* A∈Γ ([])    ¬occurs = []
strengthen* A∈Γ (t ∷ σ) ¬occurs =
  strengthen A∈Γ t (¬occurs ∘ here) ∷
  strengthen* A∈Γ σ (¬occurs ∘ there)
