{-# OPTIONS --without-K --warning=noUserWarning --warning=noUselessPrivate --warning=noUnsupportedIndexedMatch #-}

open import Level using (_⊔_;suc;lift)
open import Categories.Category using (Category)
open import Categories.Category.Monoidal using (Monoidal)
open import Categories.Category.Monoidal.Closed using (Closed)
open import Categories.Functor using (Functor; _∘F_) renaming (id to idF)

module Categories.Rosen.Functorial.Core {o ℓ e} {C : Category o ℓ e} {E : Category (o ⊔ ℓ) (ℓ ⊔ e) e} {M : Monoidal C} (Cl : Closed M) (U : Functor E C) where

-- Functorial natural MR systems

open import Data.Product using (_,_; proj₁; proj₂; _×_; Σ)
open import Relation.Binary.Bundles using (Setoid)
open import Relation.Binary.PropositionalEquality using (_≡_; subst)

open import Categories.Category.Construction.Arrow
open import Categories.Category.Instance.Setoids using (Setoids)
open import Categories.Functor.Bifunctor using (Bifunctor; appˡ; appʳ)
open import Categories.Category.Product using (Product;_⁂_;πʳ)
open import Categories.Functor.Bifunctor.Properties using ([_]-commute)
open import Categories.Morphism.Reasoning as MR
open import Categories.NaturalTransformation using (NaturalTransformation;ntHelper; _∘ᵥ_; _∘ₕ_; _∘ˡ_; _∘ʳ_) renaming (id to idN)
open import Categories.NaturalTransformation.Equivalence using (_≃_)

import Reason
open Reason C

module E = Category E
module U = Functor U

postulate
  irrelevance : ∀ {ℓ} {A : Set ℓ} → A
  
open Closed Cl using (adjoint; unitorˡ;unitorʳ-commute-to; unitorʳ-commute-from;unitorʳ; [-,-]; unit; [_,_]₀; [_,-]; [-,_]; [_,_]₁; _⊗₁_)

module Arr = Categories.Category.Construction.Arrow C

-- nHom sends f : A ⇒ B to the induced natural transformation [-,f] : [B,-] ⇒ [A,-].
nHom : ∀ {A B} → A ⇒ B → NaturalTransformation ([_,-] B) ([_,-] A)
nHom {A} {B} f = record
  { η = λ X → [ f , id ]₁
  ; commute = λ h → Equiv.sym [ [-,-] ]-commute
  ; sym-commute = λ h → [ [-,-] ]-commute
  }

-- nHom-identity: nHom respects identity.
nHom-identity : ∀ {A} → nHom (id {A}) ≃ idN
nHom-identity = [-,-].identity

-- definition of an (M,R)-system according to Rosen
record MR2 (A B : Obj) : Set (o ⊔ ℓ ⊔ e) where
  eta-equality
  constructor ⟪_,_,_⟫
  field
    f : A ⇒ B
    Φ : NaturalTransformation U ([_,-] A ∘F U)
    Ue≈f : Σ E.Obj (λ x → Σ E.Obj (λ y → Σ (x E.⇒ y) (λ e → Σ (U.F₀ x ≡ A) (λ p → Σ (U.F₀ y ≡ B) (λ q → subst (λ z → z ⇒ B) p (subst (λ z → U.F₀ x ⇒ z) q (U.F₁ e)) ≈ f)))))

  Φη = NaturalTransformation.η Φ
  Φcommute = λ {X Y : Category.Obj E} t → NaturalTransformation.commute Φ {X} {Y} t
  Φη₀ = let (_ , y , _ , _ , q , _) = Ue≈f
        in subst (λ z → z ⇒ [_,_]₀ A z) q (Φη y)

-- MR2 as a Setoid: two MR2 elements are equal when their f components are equal
-- and their Φ components are ≃-equal.
  
open import Categories.Functor.Construction.LiftSetoids using (LiftSetoids)

MR2-Setoid : Obj → Obj → Setoid (o ⊔ ℓ ⊔ e) (o ⊔ ℓ ⊔ e)
MR2-Setoid A B = record
  { Carrier = MR2 A B
  ; _≈_ = λ (⟪ f , Φ , irrelevance ⟫) (⟪ g , Φ' , irrelevance ⟫) → (f ≈ g) × (Φ ≃ Φ')
  ; isEquivalence = record
    { refl = Equiv.refl , (λ {x₁} → Equiv.refl)
    ; sym = λ (pf , k) → Equiv.sym pf , Equiv.sym k
    ; trans = λ (pf₁ , h) (pf₂ , k) → Equiv.trans pf₁ pf₂ , Equiv.trans h k
    }
  }

open HomReasoning
open MR

-- the same proof that works for Cod works in general:
MRS-Profunctor : Bifunctor (Category.op C) C (Setoids (o ⊔ ℓ ⊔ e) (o ⊔ ℓ ⊔ e))
MRS-Profunctor = record
  { F₀ = (λ { (A , B) → MR2-Setoid A B })
  ; F₁ = λ { {(A , B)} {(A' , B')} (u , v) → record
    { _⟨$⟩_ = λ {⟪ f , Φ , _ ⟫ → ⟪ v ∘ f ∘ u , (nHom u ∘ʳ U) ∘ᵥ Φ , irrelevance ⟫ }
    ; cong = λ { {⟪ f , Φ , _ ⟫} {⟪ g , Φ' , _ ⟫} (f≈g , Φ≈Φ') →
        (∘-resp-≈ Equiv.refl (∘-resp-≈ f≈g Equiv.refl))
      , (λ {x} → ∘-resp-≈ʳ (Φ≈Φ' {x}))
      }
    }}
  ; identity = λ { {(A , B)} {⟪ f , Φ , _ ⟫} {⟪ g , Φ' , _ ⟫} →
      let module Hom = Functor [-,-] in
        ( λ (f≈g , Φ≈Φ') → Equiv.trans identityˡʳ f≈g
        , λ { {h} → trans (∘-resp-≈ Hom.identity Φ≈Φ') identityˡ })
     }
  ; homomorphism = λ { {f = (u₁ , v₁)} {g = (u₂ , v₂)} {⟪ f , Φ , _ ⟫} {⟪ g , Φ' , _ ⟫} →
       let module Hom = Functor [-,-]
           module Hom[1-] {A} = Functor (appˡ [-,-] A)
           module Hom[-1] {A} = Functor (appʳ [-,-] A) in
         ( λ { (f≈g , Φ≈Φ') →
             (begin (v₂ ∘ v₁) ∘ f ∘ u₁ ∘ u₂     ≈˘⟨ assoc ○ assoc ⟩
                    (((v₂ ∘ v₁) ∘ f) ∘ u₁) ∘ u₂ ≈⟨ (refl⟩∘⟨ f≈g) ⟩∘⟨refl ⟩∘⟨refl ⟩
                    (((v₂ ∘ v₁) ∘ g) ∘ u₁) ∘ u₂ ≈⟨ (assoc ⟩∘⟨refl) ○ (assoc ⟩∘⟨refl) ⟩
                    (v₂ ∘ (v₁ ∘ (g ∘ u₁))) ∘ u₂ ≈⟨ assoc ○ sym-assoc ○ assoc ⟩
                    v₂ ∘ (v₁ ∘ g ∘ u₁) ∘ u₂     ∎)
        , λ { {h} →
            let module Φ = NaturalTransformation Φ
                module Φ' = NaturalTransformation Φ'
            in
            begin [ u₁ ∘ u₂ , id ]₁ ∘ Φ.η h              ≈⟨ ∘-resp-≈ Equiv.refl (Φ≈Φ' {h}) ⟩
                  [ u₁ ∘ u₂ , id ]₁ ∘ Φ'.η h             ≈⟨ Hom[-1].homomorphism ⟩∘⟨refl ⟩
                  ([ u₂ , id ]₁ ∘ [ u₁ , id ]₁) ∘ Φ'.η h ≈⟨ assoc ⟩
                  [ u₂ , id ]₁ ∘ ([ u₁ , id ]₁ ∘ Φ'.η h) ∎ } })
     }
  ; F-resp-≈ = λ { {(A , B)} {(A' , B')} {f = (u , v)} {g = (u' , v')} (u≈u' , v≈v') {⟪ f , Φ , _ ⟫} {⟪ g , Φ' , _ ⟫} →
       let module Hom = Functor [-,-] in
         ( λ { (f≈g , Φ≈Φ') → ∘-resp-≈ v≈v' (∘-resp-≈ f≈g u≈u')
        , λ { {h} →
            let module Φ = NaturalTransformation Φ
                module Φ' = NaturalTransformation Φ'
            in ∘-resp-≈ (Hom.F-resp-≈ (u≈u' , Equiv.refl)) (Φ≈Φ' {h})
              } })
     }
  }