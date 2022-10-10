{-# OPTIONS --safe --without-K #-}

import LambdaFrex.Types as Types

module LambdaFrex.Terms.Properties
  {a} (G : Set a)
  (let open Types G)
  where

open import LambdaFrex.Bundles G
open import LambdaFrex.Category G
import LambdaFrex.Terms G as Terms renaming (_≈_ to ₍_₎_≈_)
import LambdaFrex.Terms.Morphism G as Morphs

open import Data.Fin using (zero; suc)
open import Data.Nat using (ℕ)
open import Data.Product using (∃; _×_; _,_)
open import Data.Vec.Membership.Reflexive
open import Data.Vec.Relation.Unary.All
open import Data.Vec.Relation.Unary.All.Ext
open import Data.Vec.Relation.Unary.All.Relation.Binary.Pointwise
open import Function as Fun using (_∘_)
open import Level using (_⊔_)
open import Relation.Binary.Indexed.Homogeneous
open import Relation.Binary.PropositionalEquality as ≡ using (_≡_; module ≡-Reasoning)

open import Categories.Adjoint using (_⊣_)
open import Categories.Category
open import Categories.Category.Instance.IndexedSetoids (∃ Context × Type) renaming (_≃_ to _≃ᵢ_)
open import Categories.Functor
open import Categories.NaturalTransformation

open ≡-Reasoning

private
  variable
    n : ℕ
    Γ Δ : Context n
    A : Type

free : ∀ {b ℓ} → Functor (IndexedSetoids b ℓ) (LambdaAlg (a ⊔ b) (a ⊔ b ⊔ ℓ))
free {b} {ℓ} = record
  { F₀ = Terms.algebra
  ; F₁ = Morphs.arr
  ; identity = pw (identity _)
  ; homomorphism = pw (homomorphism _)
  ; F-resp-≈ = λ f≃g → pw (resp-≈ f≃g _)
  }
  where
  module _ {S : IndexedSetoid (∃ Context × Type) b ℓ} where
    identity : (t : Terms.Term S Γ A) →
      Terms.₍ S ₎ Morphs.⟦ Category.id (IndexedSetoids b ℓ) ⟧ t ≈ t
    identity* : (σ : All (Terms.Term S Γ) Δ) →
      Pointwise (Terms.₍ S ₎_≈_) (Morphs.⟦ Category.id (IndexedSetoids b ℓ) ⟧* σ) σ

    identity (Terms.meta m)    = Terms.refl
    identity (Terms.subst σ t) = Terms.subst-cong (identity* σ) (identity t)
    identity (Terms.var A∈Γ)   = Terms.refl
    identity (Terms.ƛ t)       = Terms.ƛ-cong (identity t)
    identity (t Terms.$ t₁)    = Terms.$-cong (identity t) (identity t₁)

    identity* []      = []
    identity* (t ∷ σ) = identity t ∷ identity* σ

  module _
    {S S₁ S₂ : IndexedSetoid (∃ Context × Type) b ℓ}
    {f : Morphism S₁ S₂} {g : Morphism S S₁}
    where
    homomorphism :
      (t : Terms.Term S Γ A) →
      Terms.₍ S₂ ₎ Morphs.⟦ IndexedSetoids b ℓ [ f ∘ g ] ⟧ t ≈ Morphs.⟦ f ⟧ (Morphs.⟦ g ⟧ t)
    homomorphism* :
      (σ : All (Terms.Term S Γ) Δ) →
      Pointwise (Terms.₍ S₂ ₎_≈_)
        (Morphs.⟦ IndexedSetoids b ℓ [ f ∘ g ] ⟧* σ)
        (Morphs.⟦ f ⟧* (Morphs.⟦ g ⟧* σ))

    homomorphism (Terms.meta m)    = Terms.refl
    homomorphism (Terms.subst σ t) = Terms.subst-cong (homomorphism* σ) (homomorphism t)
    homomorphism (Terms.var A∈Γ)   = Terms.refl
    homomorphism (Terms.ƛ t)       = Terms.ƛ-cong (homomorphism t)
    homomorphism (t Terms.$ t₁)    = Terms.$-cong (homomorphism t) (homomorphism t₁)

    homomorphism* []      = []
    homomorphism* (t ∷ σ) = homomorphism t ∷ homomorphism* σ

  module _
    {S S₁ : IndexedSetoid (∃ Context × Type) b ℓ} {f g : Morphism S S₁}
    (f≃g : f ≃ᵢ g)
    where
    resp-≈ : (t : Terms.Term S Γ A) → Terms.₍ S₁ ₎ Morphs.⟦ f ⟧ t ≈ Morphs.⟦ g ⟧ t
    resp-≈* : (σ : All (Terms.Term S Γ) Δ) →
      Pointwise (Terms.₍ S₁ ₎_≈_) (Morphs.⟦ f ⟧* σ) (Morphs.⟦ g ⟧* σ)

    resp-≈ (Terms.meta m)    = Terms.meta-cong (f≃g .at)
    resp-≈ (Terms.subst σ t) = Terms.subst-cong (resp-≈* σ) (resp-≈ t)
    resp-≈ (Terms.var A∈Γ)   = Terms.refl
    resp-≈ (Terms.ƛ t)       = Terms.ƛ-cong (resp-≈ t)
    resp-≈ (t Terms.$ t₁)    = Terms.$-cong (resp-≈ t) (resp-≈ t₁)

    resp-≈* []      = []
    resp-≈* (t ∷ σ) = resp-≈ t ∷ resp-≈* σ

free⊣forget : ∀ {b ℓ} → free {a ⊔ b} {a ⊔ b ⊔ ℓ} ⊣ forget {a ⊔ b} {a ⊔ b ⊔ ℓ}
free⊣forget {b} {ℓ} = record
  { unit = ntHelper (record
    { η = unit
    ; commute = λ f → pw Terms.refl
    })
  ; counit = ntHelper (record
    { η = counit
    ; commute = λ f → pw (λ {_ _ _ t} → eval-commute f t)
    })
  ; zig = pw (zig _ _)
  ; zag = λ {A} → pw (LambdaAlgebra.≈.refl A)
  }
  where

  unit : ∀ X → Morphism X (forget.₀ (Terms.algebra X) )
  unit X = record { ⟦_⟧ = Terms.meta ; cong = Terms.meta-cong }

  module _ (X : LambdaAlgebra (a ⊔ b) (a ⊔ b ⊔ ℓ)) where
    open LambdaAlgebra X

    eval : Terms.Term (forget.₀ X) Γ A → T Γ A
    eval* : All (Terms.Term (forget.₀ X) Γ) Δ → All (T Γ) Δ

    eval (Terms.meta m)    = m
    eval (Terms.subst σ t) = subst (eval* σ) (eval t)
    eval (Terms.var A∈Γ)   = var A∈Γ
    eval (Terms.ƛ t)       = ƛ (eval t)
    eval (t Terms.$ t₁)    = eval t $ eval t₁

    eval* []      = []
    eval* (t ∷ σ) = eval t ∷ eval* σ

    eval*≡map[eval] : (σ : All (Terms.Term (forget.₀ X) Γ) Δ) → eval* σ ≡ map eval σ
    eval*≡map[eval] []      = ≡.refl
    eval*≡map[eval] (t ∷ σ) = ≡.cong (eval t ∷_) (eval*≡map[eval] σ)

    eval-cong : ∀ {t t₁ : Terms.Term (forget.₀ X) Γ A} →
      Terms.₍ forget.₀ X ₎ t ≈ t₁ → eval t ≈ eval t₁
    eval*-cong : ∀ {γ δ : All (Terms.Term (forget.₀ X) Γ) Δ} →
      Pointwise (Terms.₍ forget.₀ X ₎_≈_) γ δ → Pointwise _≈_ (eval* γ) (eval* δ)

    eval-cong Terms.refl                  = ≈.refl
    eval-cong (Terms.sym t≈t₁)            = ≈.sym (eval-cong t≈t₁)
    eval-cong (Terms.trans t≈t₁ t≈t₂)     = ≈.trans (eval-cong t≈t₁) (eval-cong t≈t₂)
    eval-cong (Terms.meta-cong m≈m₁)      = m≈m₁
    eval-cong (Terms.subst-cong γ≈δ t≈t₁) = subst-cong (eval*-cong γ≈δ) (eval-cong t≈t₁)
    eval-cong (Terms.ƛ-cong t≈t₁)         = ƛ-cong (eval-cong t≈t₁)
    eval-cong (Terms.$-cong t≈t₁ t≈t₂)    = $-cong (eval-cong t≈t₁) (eval-cong t≈t₂)
    eval-cong (Terms.subst-∘ γ δ t)       = ≈.trans
      (subst-∘ (eval* γ) (eval* δ) (eval t))
      (subst-congˡ (reflexive ≈.reflexive (≡⇒Pointwise≡ (begin
        map (subst (eval* γ)) (eval* δ)    ≡⟨  ≡.cong (map _) (eval*≡map[eval] δ) ⟩
        map (subst (eval* γ)) (map eval δ) ≡⟨  map-∘ (subst (eval* γ)) eval δ ⟩
        map (subst (eval* γ) ∘ eval) δ     ≡⟨⟩
        map (eval ∘ Terms.subst γ) δ       ≡˘⟨ map-∘ eval (Terms.subst γ) δ ⟩
        map eval (map (Terms.subst γ) δ)   ≡˘⟨ eval*≡map[eval] (map (Terms.subst γ) δ) ⟩
        eval* (map (Terms.subst γ) δ)      ∎))))
    eval-cong (Terms.subst-var γ A∈Γ)     = ≈.trans
      (subst-var (eval* γ) A∈Γ)
      (≈.reflexive (begin
        lookup-∈ (eval* γ) A∈Γ    ≡⟨ ≡.cong (λ σ → lookup-∈ σ A∈Γ) (eval*≡map[eval] γ) ⟩
        lookup-∈ (map eval γ) A∈Γ ≡⟨ lookup-∈-map eval γ A∈Γ ⟩
        eval (lookup-∈ γ A∈Γ)     ∎))
    eval-cong (Terms.subst-ƛ γ t)         = ≈.trans
      (subst-ƛ (eval* γ) (eval t))
      (ƛ-cong (subst-congˡ (≈.refl ∷ reflexive ≈.reflexive (≡⇒Pointwise≡ (begin
        wkn (eval* γ)                                 ≡⟨⟩
        map (weaken zero) (eval* γ)                   ≡⟨  ≡.cong (map _) (eval*≡map[eval] γ) ⟩
        map (weaken zero) (map eval γ)                ≡⟨  map-∘ _ eval γ ⟩
        map (weaken zero ∘ eval) γ                    ≡⟨  map-cong
          (λ t → ≡.cong (λ σ → subst σ (eval t)) (begin
            tabulate (var ∘ ∈-lookup ∘ suc)                   ≡⟨⟩
            tabulate (eval ∘ Terms.var ∘ ∈-lookup ∘ suc)      ≡˘⟨ tabulate-∘ eval _ ⟩
            map eval (tabulate (Terms.var ∘ ∈-lookup ∘ suc))  ≡˘⟨ eval*≡map[eval] _ ⟩
            eval* (tabulate (Terms.var ∘ ∈-lookup ∘ suc))     ∎))
          γ ⟩
        map (eval ∘ Terms.weaken (forget.₀ X) zero) γ ≡˘⟨ map-∘ eval _ γ ⟩
        map eval (Terms.wkn (forget.₀ X) γ)           ≡˘⟨ eval*≡map[eval] _ ⟩
        eval* (Terms.wkn (forget.₀ X) γ)              ∎)))))
    eval-cong (Terms.subst-$ γ t t₁)      = subst-$ (eval* γ) (eval t) (eval t₁)
    eval-cong (Terms.⟶-β t t₁)            = ≈.trans
      (⟶-β (eval t) (eval t₁))
      (subst-congˡ (≈.refl ∷ reflexive ≈.reflexive (≡⇒Pointwise≡ (begin
        tabulate (var ∘ ∈-lookup)                   ≡⟨⟩
        tabulate (eval ∘ Terms.var ∘ ∈-lookup)      ≡˘⟨ tabulate-∘ eval _ ⟩
        map eval (tabulate (Terms.var ∘ ∈-lookup))  ≡˘⟨ eval*≡map[eval] _ ⟩
        eval* (tabulate (Terms.var ∘ ∈-lookup))     ∎))))
    eval-cong (Terms.⟶-η t)               = ≈.trans
      (ƛ-cong ($-congˡ (subst-congˡ (reflexive ≈.reflexive (≡⇒Pointwise≡ (begin
        eval* (tabulate (Terms.var ∘ ∈-lookup ∘ suc))     ≡⟨ eval*≡map[eval] _ ⟩
        map eval (tabulate (Terms.var ∘ ∈-lookup ∘ suc))  ≡⟨ tabulate-∘ eval _ ⟩
        tabulate (eval ∘ Terms.var ∘ ∈-lookup ∘ suc)      ≡⟨⟩
        tabulate (var ∘ ∈-lookup ∘ suc)                   ∎))))))
      (⟶-η (eval t))

    eval*-cong []           = []
    eval*-cong (t≈t₁ ∷ γ≈δ) = eval-cong t≈t₁ ∷ eval*-cong γ≈δ

    counit : Lambda⇒ (Terms.algebra (forget.₀ X)) X
    counit = record
      { ⟦_⟧ = eval
      ; cong = eval-cong
      ; subst-homo = λ γ t → subst-congˡ (reflexive ≈.reflexive (≡⇒Pointwise≡ (eval*≡map[eval] γ)))
      ; var-homo = λ _ → ≈.refl
      ; ƛ-homo = λ _ → ≈.refl
      ; $-homo = λ _ _ → ≈.refl
      }

  module _ {X Y : LambdaAlgebra (a ⊔ b) (a ⊔ b ⊔ ℓ)} (f : Lambda⇒ X Y) where
    open Lambda⇒ f
    private
      module X = LambdaAlgebra X
      module Y = LambdaAlgebra Y

    eval-commute : ∀ (t : Terms.Term (forget.₀ X) Γ A) →
      eval Y (Morphs.⟦ forget.₁ f ⟧ t) Y.≈ ⟦ eval X t ⟧
    eval*-commute : ∀ (σ : All (Terms.Term (forget.₀ X) Γ) Δ) →
      Pointwise Y._≈_ (eval* Y (Morphs.⟦ forget.₁ f ⟧* σ)) (map ⟦_⟧ (eval* X σ))

    eval-commute (Terms.meta m)    = Y.≈.refl
    eval-commute (Terms.subst σ t) = Y.≈.trans
      (Y.subst-cong (eval*-commute σ) (eval-commute t))
      (Y.≈.sym (subst-homo (eval* X σ) (eval X t)))
    eval-commute (Terms.var A∈Γ)   = Y.≈.sym (var-homo A∈Γ)
    eval-commute (Terms.ƛ t)       = Y.≈.trans
      (Y.ƛ-cong (eval-commute t))
      (Y.≈.sym (ƛ-homo (eval X t)))
    eval-commute (t Terms.$ t₁)    = Y.≈.trans
      (Y.$-cong (eval-commute t) (eval-commute t₁))
      (Y.≈.sym ($-homo (eval X t) (eval X t₁)))

    eval*-commute []      = []
    eval*-commute (t ∷ σ) = eval-commute t ∷ eval*-commute σ

  module _ (S : IndexedSetoid (∃ Context × Type) (a ⊔ b) (a ⊔ b ⊔ ℓ)) where
    open IndexedSetoid S

    zig : (t : Terms.Term S Γ A) →
      Terms.₍ S ₎ eval (Functor.F₀ free S) (Morphs.⟦ unit S ⟧ t) ≈ t
    zig* : (σ : All (Terms.Term S Γ) Δ) →
      Pointwise Terms.₍ S ₎_≈_ (eval* (Functor.F₀ free S) (Morphs.⟦ unit S ⟧* σ)) σ

    zig (Terms.meta m)    = Terms.refl
    zig (Terms.subst σ t) = Terms.subst-cong (zig* σ) (zig t)
    zig (Terms.var A∈Γ)   = Terms.refl
    zig (Terms.ƛ t)       = Terms.ƛ-cong (zig t)
    zig (t Terms.$ t₁)    = Terms.$-cong (zig t) (zig t₁)

    zig* []      = []
    zig* (t ∷ σ) = zig t ∷ zig* σ
