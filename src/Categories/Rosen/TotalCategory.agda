{-# OPTIONS --without-K --safe --warning=noUserWarning --warning=noUselessPrivate #-}

open import Level using (_⊔_)
open import Categories.Category using (Category)
open import Categories.Category.Monoidal using (Monoidal)
open import Categories.Category.Monoidal.Closed using (Closed)

module Categories.Rosen.TotalCategory {o ℓ e} {C : Category o ℓ e} {M : Monoidal C} (Cl : Closed M) where

open Category C

open import Data.Product using (_,_; _×_)

open import Categories.Category.Construction.Arrow
open import Categories.Functor using (Functor)
open import Categories.Functor.Bifunctor using (appʳ)
open import Categories.Functor.Bifunctor.Properties using ([_]-commute)
open import Categories.Functor.Profunctor.Tabulator
open import Categories.Morphism.Reasoning as MR
open import Categories.NaturalTransformation using (_∘ᵥ_; _∘ʳ_) renaming (NaturalTransformation to NT)
open import Categories.Rosen.Core Cl

open Closed Cl using ([-,-]; [_,-]; [_,_]₁)
open HomReasoning
open MR

-- The total category of the MRS-profunctor tabulator.
-- Equivalent to the tabulator of MRS-Profunctor (see Tabulator.agda).

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
  module l*ψ = NT ((nHom l ∘ʳ Cod) ∘ᵥ MR2.Φ y.ξ)
  
  field
    eqf : r ∘ f ≈ g ∘ l
    nat : ∀ {s t} (α : Arr.Morphism⇒ s t)
        → l*ψ.η t ∘ Arr.Morphism⇒.cod⇒ α
        ≈ Functor.F₁ [ x.L ,-] (Arr.Morphism⇒.cod⇒ α) ∘ Φ.η s
  
  eqΦ : ∀ {t} → l*ψ.η t ≈ Φ.η t
  eqΦ {t} =
    Equiv.sym identityʳ
    ○ nat (Category.id Arr.Arrow {A = t})
    ○ elimˡ C [-,-].identity


total : Category (o ⊔ ℓ ⊔ e) (o ⊔ ℓ ⊔ e) e
total = record
  { Obj = tab₀ MRS-Profunctor
  ; _⇒_ = λ s t → tot⇒ s t
  ; _≈_ = λ h k → tot⇒.l h ≈ tot⇒.l k × tot⇒.r h ≈ tot⇒.r k
  ; id = λ { {(A , B) ∣ ⟪ f , Φ ⟫} → 
       let module ΦNT = NT Φ
           module l*Φ = NT ((nHom id ∘ʳ Cod) ∘ᵥ Φ)
       in
       [ id , id
       ∥ id-comm-sym C
       , (λ {s} {t} α → 
         elimˡ C [-,-].identity ⟩∘⟨refl 
         ○ ΦNT.commute α)
       ]}
  ; _∘_ = λ { {A} {B} {X} t t' →
       let module t  = tot⇒ t
           module t' = tot⇒ t'
           module ψ  = NT (MR2.Φ t.y.ξ)
           module Hom[-1] {X} = Functor (appʳ [-,-] X)
           module Hx = Functor [ t'.x.L ,-]
           module Hy = Functor [ t.x.L ,-]
       in
       [ t.l ∘ t'.l , t.r ∘ t'.r ∥ 
         pullʳ C t'.eqf ○ pullˡ C t.eqf ○ assoc
       , (λ {s} {t₀} α →
           let r = Arr.Morphism⇒.cod⇒ α in
           begin
             ([ t.l ∘ t'.l , id ]₁ ∘ ψ.η t₀) ∘ r             ≈⟨ ∘-resp-≈ (∘-resp-≈ (Hom[-1].homomorphism) Equiv.refl) Equiv.refl ⟩
             (([ t'.l , id ]₁ ∘ [ t.l , id ]₁) ∘ ψ.η t₀) ∘ r ≈⟨ ∘-resp-≈ assoc Equiv.refl ○ assoc ⟩
             [ t'.l , id ]₁ ∘ (([ t.l , id ]₁ ∘ ψ.η t₀) ∘ r) ≈⟨ (refl⟩∘⟨ t.nat α) ○  sym-assoc ⟩
            ([ t'.l , id ]₁ ∘ Hy.F₁ r) ∘ t.Φ.η s             ≈⟨ (∘-resp-≈ (Equiv.sym [ [-,-] ]-commute) Equiv.refl) ○ assoc ⟩
             Hx.F₁ r ∘ ([ t'.l , id ]₁ ∘ t.Φ.η s)            ≈⟨ refl⟩∘⟨ t'.eqΦ {t = s} ⟩
             Hx.F₁ r ∘ t'.Φ.η s                              ∎)
       ]}
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