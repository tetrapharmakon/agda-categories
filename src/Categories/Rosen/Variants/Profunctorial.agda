{-# OPTIONS --without-K --warning=noUserWarning --warning=noUselessPrivate --warning=noUnsupportedIndexedMatch #-}

open import Categories.Category using (Category)
open import Categories.Category.Instance.Setoids using (Setoids)
open import Categories.Category.Monoidal using (Monoidal)
open import Categories.Category.Monoidal.Closed using (Closed)
open import Categories.Functor using (Functor; _∘F_) renaming (id to idF)
open import Categories.Functor.Bifunctor using (Bifunctor; appˡ; appʳ)
open import Level using (_⊔_;suc)

module Categories.Rosen.Variants.Profunctorial {o ℓ e} {C E : Category o ℓ e} {M : Monoidal C} (Cl : Closed M) where

private
  postulate
    sorry : ∀ {u} {A : Set u} → A

open import Categories.Category.CoSlice C
open import Categories.Category.Slice C

-- Functorial natural MR systems

open import Data.Product using (Σ;_,_;proj₁;proj₂;_×_)
open import Relation.Binary.Bundles using (Setoid)

open import Categories.Category.Construction.Arrow
open import Categories.Category.Product using (Product;_⁂_;πʳ)
open import Categories.Functor.Bifunctor.Properties using ([_]-commute)
open import Categories.Functor.Hom
open import Categories.Morphism.Reasoning as MR
open import Categories.NaturalTransformation using (NaturalTransformation;ntHelper; _∘ᵥ_; _∘ₕ_; _∘ˡ_; _∘ʳ_;F⇒F∘id) renaming (id to idN)
open import Categories.NaturalTransformation.Equivalence using (_≃_)
import Reason
open Reason C

open Closed Cl using (adjoint; unitorˡ;unitorʳ-commute-to; unitorʳ-commute-from;unitorʳ; [-,-]; unit; [_,_]₀; [_,-]; [-,_]; [_,_]₁; _⊗₁_)

-- module Arr = Categories.Category.Construction.Arrow C

-- -- nHom sends f : A ⇒ B to the induced natural transformation [-,f] : [B,-] ⇒ [A,-].
-- nHom : ∀ {A B} → A ⇒ B → NaturalTransformation ([_,-] B) ([_,-] A)
-- nHom {A} {B} f = record
--   { η = λ X → [ f , id ]₁
--   ; commute = λ h → Equiv.sym [ [-,-] ]-commute
--   ; sym-commute = λ h → [ [-,-] ]-commute
--   }

-- -- nHom-identity: nHom respects identity.
-- nHom-identity : ∀ {A} → nHom (id {A}) ≃ idN
-- nHom-identity = [-,-].identity

conjoint[_,-] : (A : Obj) {B : Obj} → Bifunctor (Category.op (coSlice A)) (Slice B)  (Setoids ℓ e)
conjoint[ A ,-] {B} = (Hom[ C ][-,-] ∘F (Functor.op (Cod A)  ⁂ ([_,-] A ∘F Dom B)))

C/B×A/C : {A B : Obj} → Category (o ⊔ ℓ) (ℓ ⊔ e) (e ⊔ e)
C/B×A/C {A} {B} = Product (Category.op (coSlice A)) (Slice B)

-- definition of a profunctorial (M,R)-system
record MR2 (A B : Obj) : Set (o ⊔ suc ℓ ⊔ suc e) where
  constructor ⟪_,_,_⟫
  field
    f : A ⇒ B
    p : Bifunctor (Category.op (coSlice A)) (Slice B) (Setoids ℓ e)
    Φ : NaturalTransformation p (conjoint[ A ,-] {B})
  Φη = NaturalTransformation.η Φ
  -- Φcommute = λ {X : Category.Obj (C/B×A/C {A} {B})} t → NaturalTransformation.commute Φ {X} t


open import Categories.NaturalTransformation.NaturalIsomorphism as NI using (NaturalIsomorphism;niHelper; _ⓘˡ_; _ⓘʳ_)

-- MR2 as a Setoid: two MR2 elements are equal when their f components are equal, their associated profunctors are isomorphic,
-- and their Φ components are ≃-equal.
MR2-Setoid : Obj → Obj → Setoid (o ⊔ suc ℓ ⊔ suc e) (o ⊔ ℓ ⊔ e) -- (o ⊔ ℓ ⊔ e) (o ⊔ ℓ ⊔ e)
MR2-Setoid A B = record
  { Carrier = MR2 A B
  ; _≈_ = λ (⟪ f , p , Φ ⟫) (⟪ g , q , Φ' ⟫) → 
   (f ≈ g) × (Σ (NaturalIsomorphism p q) 
     (λ t → let τ = NI.NaturalIsomorphism.F⇒G t 
            in Φ ≃ Φ' ∘ᵥ τ))
  ; isEquivalence = record 
    { refl = refl , NI.refl , λ t → {!   !}
    ; sym = λ (a , b , c) → (sym a) , NI.sym b , {!   !}
    ; trans = λ (a , b , c) (a' , b' , c') → (trans a a') , NI.trans b b' , {!   !} -- trans , NI.trans , {!   !} 
    }
  } 

pollo : ∀ {A' A B B'} {u : A' ⇒ A} {v : B ⇒ B'} → Functor (Product (Category.op (coSlice A)) (Slice B)) (Product (Category.op (coSlice A')) (Slice B'))
pollo {u = u} {v = v} = Functor.op (u /C) ⁂ (C/ v)

open HomReasoning
open MR
-- -- the same proof that works for Cod works in general
MRS-Profunctor : Bifunctor (Category.op C) C (Setoids (o ⊔ suc ℓ ⊔ suc e) (o ⊔ ℓ ⊔ e))
MRS-Profunctor = record
  { F₀ = (λ { (A , B) → MR2-Setoid A B })
  ; F₁ = λ { {(A , B)} {(A' , B')} (u , v) → record
    { _⟨$⟩_ = λ {⟪ f , p , Φ ⟫ → ⟪ v ∘ f ∘ u , {!   !} ∘F p ∘F {!   !} , {!   !} ⟫ }
    ; cong = λ { {⟪ f , p , Φ ⟫} {⟪ g , q , Φ' ⟫} (f≈g , Φ≈Φ') →
        (∘-resp-≈ Equiv.refl (∘-resp-≈ f≈g Equiv.refl))
      , niHelper (record 
          { η = λ X → {!   !} 
          ; η⁻¹ = λ X → {!   !} 
          ; commute = λ f₁ x → {!   !} 
          ; iso = {!   !} 
          }) -- (λ {x} → ∘-resp-≈ʳ (Φ≈Φ' {x}))
      , {!   !}
      }
    }}
  ; identity = {!   !}
  ; homomorphism = {!   !}
  ; F-resp-≈ = {!   !}
  } -- record
  -- { F₀ = (λ { (A , B) → MR2-Setoid A B })
  -- ; F₁ = λ { {(A , B)} {(A' , B')} (u , v) → record
  --   { _⟨$⟩_ = λ {⟪ f , p , Φ ⟫ → ⟪ v ∘ f ∘ u , ? , ? ⟫ }
  --   ; cong = λ { {⟪ f , Φ ⟫} {⟪ g , Φ' ⟫} (f≈g , Φ≈Φ') →
  --       (∘-resp-≈ Equiv.refl (∘-resp-≈ f≈g Equiv.refl))
  --     , (λ {x} → ∘-resp-≈ʳ (Φ≈Φ' {x}))
  --     }
  --   }}
  -- ; identity = λ { {(A , B)} {⟪ f , Φ ⟫} {⟪ g , Φ' ⟫} →
  --     let module Hom = Functor [-,-] in
  --       ( λ (f≈g , Φ≈Φ') → Equiv.trans identityˡʳ f≈g
  --       , λ { {h} → trans (∘-resp-≈ Hom.identity Φ≈Φ') identityˡ })
  --    }
  -- ; homomorphism = λ { {f = (u₁ , v₁)} {g = (u₂ , v₂)} {⟪ f , Φ ⟫} {⟪ g , Φ' ⟫} →
  --      let module Hom = Functor [-,-]
  --          module Hom[1-] {A} = Functor (appˡ [-,-] A)
  --          module Hom[-1] {A} = Functor (appʳ [-,-] A) in
  --        ( λ { (f≈g , Φ≈Φ') →
  --            (begin (v₂ ∘ v₁) ∘ f ∘ u₁ ∘ u₂     ≈˘⟨ assoc ○ assoc ⟩
  --                   (((v₂ ∘ v₁) ∘ f) ∘ u₁) ∘ u₂ ≈⟨ (refl⟩∘⟨ f≈g) ⟩∘⟨refl ⟩∘⟨refl ⟩
  --                   (((v₂ ∘ v₁) ∘ g) ∘ u₁) ∘ u₂ ≈⟨ (assoc ⟩∘⟨refl) ○ (assoc ⟩∘⟨refl) ⟩
  --                   (v₂ ∘ (v₁ ∘ (g ∘ u₁))) ∘ u₂ ≈⟨ assoc ○ sym-assoc ○ assoc ⟩
  --                   v₂ ∘ (v₁ ∘ g ∘ u₁) ∘ u₂     ∎)
  --       , λ { {h} →
  --           let module Φ = NaturalTransformation Φ
  --               module Φ' = NaturalTransformation Φ'
  --           in
  --           begin [ u₁ ∘ u₂ , id ]₁ ∘ Φ.η h              ≈⟨ ∘-resp-≈ Equiv.refl (Φ≈Φ' {h}) ⟩
  --                 [ u₁ ∘ u₂ , id ]₁ ∘ Φ'.η h             ≈⟨ Hom[-1].homomorphism ⟩∘⟨refl ⟩
  --                 ([ u₂ , id ]₁ ∘ [ u₁ , id ]₁) ∘ Φ'.η h ≈⟨ assoc ⟩
  --                 [ u₂ , id ]₁ ∘ ([ u₁ , id ]₁ ∘ Φ'.η h) ∎ } })
  --    }
  -- ; F-resp-≈ = λ { {(A , B)} {(A' , B')} {f = (u , v)} {g = (u' , v')} (u≈u' , v≈v') {⟪ f , Φ ⟫} {⟪ g , Φ' ⟫} →
  --      let module Hom = Functor [-,-] in
  --        ( λ { (f≈g , Φ≈Φ') → ∘-resp-≈ v≈v' (∘-resp-≈ f≈g u≈u')
  --       , λ { {h} →
  --           let module Φ = NaturalTransformation Φ
  --               module Φ' = NaturalTransformation Φ'
  --           in ∘-resp-≈ (Hom.F-resp-≈ (u≈u' , Equiv.refl)) (Φ≈Φ' {h})
  --             } })
  --    }
  -- }