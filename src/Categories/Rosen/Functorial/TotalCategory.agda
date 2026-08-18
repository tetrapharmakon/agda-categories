{-# OPTIONS --without-K --warning=noUserWarning --warning=noUselessPrivate --warning=noUnsupportedIndexedMatch #-}

open import Categories.Category using (Category)
open import Categories.Category.Monoidal using (Monoidal)
open import Categories.Category.Monoidal.Closed using (Closed)
open import Categories.Functor using (Functor;_∘F_)
open import Level using (_⊔_)

module Categories.Rosen.Functorial.TotalCategory {o ℓ e} {C : Category o ℓ e} {E : Category (o ⊔ ℓ) (ℓ ⊔ e) e} {M : Monoidal C} (Cl : Closed M) (U : Functor E C) where

open Category C

module U = Functor U

open import Data.Product using (_,_; _×_)

open import Categories.Category.Construction.Arrow
open import Categories.Functor.Bifunctor using (appʳ)
open import Categories.Functor.Bifunctor.Properties using ([_]-commute)
open import Categories.Functor.Profunctor.Tabulator using (tab₀; tab⇒)
open import Categories.Morphism.Reasoning as MR
open import Categories.NaturalTransformation using (_∘ᵥ_; _∘ʳ_) renaming (NaturalTransformation to NT)
open import Categories.Rosen.Functorial.Core Cl U using (nHom; MR2; MRS-Profunctor)

open Closed Cl using ([-,-]; [_,-]; [_,_]₁)

-- The total category of the (functorial) MRS-profunctor tabulator.
-- Equivalent to the tabulator of MRS-Profunctor (see Tabulator.agda).

open HomReasoning
open MR

record tot⇒ (x y : tab₀ MRS-Profunctor) : Set (o ⊔ ℓ ⊔ e) where
  constructor [_,_∥_,_]
  module x = tab₀ x
  module y = tab₀ y
  field
    l : x.L ⇒ y.L
    r : x.R ⇒ y.R

  f = MR2.f x.ξ
  g = MR2.f y.ξ

  module Φ = NT (MR2.Φ x.ξ)
  module ψ = NT (MR2.Φ y.ξ)
  module l*ψ = NT ((nHom l ∘ʳ U) ∘ᵥ MR2.Φ y.ξ)

  field
    eqf : r ∘ f ≈ g ∘ l
    nat : ∀ {s t : Category.Obj E} (h : Category._⇒_ E s t) → l*ψ.η t ∘ U.F₁ h ≈ Functor.F₁ [ x.L ,-] (U.F₁ h) ∘ Φ.η s

  eqΦ : ∀ {t} → l*ψ.η t ≈ Φ.η t
  eqΦ {t} = introʳ C U.identity ○ nat (Category.id E) ○ elimˡ C (Functor.identity ([ _ ,-] ∘F U))


total : Category (o ⊔ ℓ ⊔ e) (o ⊔ ℓ ⊔ e) e
total = record
  { Obj = tab₀ MRS-Profunctor
  ; _⇒_ = λ s t → tot⇒ s t
  ; _≈_ = λ h k → tot⇒.l h ≈ tot⇒.l k × tot⇒.r h ≈ tot⇒.r k
  ; id = λ { {A} → 
    let module A = tab₀ A
        module Φ = NT (MR2.Φ A.ξ) 
    in [ id , id ∥ (id-comm-sym C) , ((λ α → elimˡ C [-,-].identity ⟩∘⟨refl ○ Φ.commute α)) ] }
  ; _∘_ = λ { {A} {B} {X} t t' →
       let module t  = tot⇒ t
           module t' = tot⇒ t'
           module ψ  = NT (MR2.Φ t.y.ξ)
           module Hom[-1] {X} = Functor (appʳ [-,-] X)
           module Hx = Functor [ t'.x.L ,-]
           module Hy = Functor [ t.x.L ,-]
       in [ t.l ∘ t'.l , t.r ∘ t'.r 
          ∥ pullʳ C t'.eqf ○ pullˡ C t.eqf ○ assoc 
          , (λ {s} {t} h → 
            begin ([ t.l ∘ t'.l , id ]₁ ∘ ψ.η t) ∘ U.F₁ h             ≈⟨ (Hom[-1].homomorphism ⟩∘⟨refl) ⟩∘⟨refl ⟩ 
                  (([ t'.l , id ]₁ ∘ [ t.l , id ]₁) ∘ ψ.η t) ∘ U.F₁ h ≈⟨ ∘-resp-≈ˡ assoc ○ assoc ⟩ 
                  [ t'.l , id ]₁ ∘ ([ t.l , id ]₁ ∘ ψ.η t) ∘ U.F₁ h   ≈⟨ (refl⟩∘⟨ t.nat h) ○  sym-assoc ⟩ 
                  ([ t'.l , id ]₁ ∘ [ id , U.F₁ h ]₁) ∘ t'.ψ.η s      ≈⟨ ∘-resp-≈ˡ (Equiv.sym [ [-,-] ]-commute) ○ assoc ⟩ 
                  [ id , U.F₁ h ]₁ ∘ t'.l*ψ.η s                       ≈⟨ refl⟩∘⟨ t'.eqΦ {t = s} ⟩ 
                  [ id {t'.x.L} , (U.F₁ h) ]₁ ∘ t'.Φ.η s              ∎) ]
      }
  ; assoc = assoc , assoc
  ; sym-assoc = sym-assoc , sym-assoc
  ; identityˡ = identityˡ , identityˡ
  ; identityʳ = identityʳ , identityʳ
  ; identity² = identity² , identity²
  ; equiv = record
    { refl = Equiv.refl , Equiv.refl
    ; sym = λ { (p , q) → Equiv.sym p , Equiv.sym q }
    ; trans = λ { (p₁ , q₁) (p₂ , q₂) → Equiv.trans p₁ p₂ , Equiv.trans q₁ q₂ }
    }
  ; ∘-resp-≈ = λ { (p₁ , q₁) (p₂ , q₂) → ∘-resp-≈ p₁ p₂ , ∘-resp-≈ q₁ q₂ }
  }
