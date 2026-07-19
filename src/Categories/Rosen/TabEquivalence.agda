{-# OPTIONS --without-K --safe --warning=noUserWarning --warning=noUselessPrivate #-}

open import Level using (_⊔_)
open import Categories.Category using (Category)
open import Categories.Category.Monoidal using (Monoidal)
open import Categories.Category.Monoidal.Closed using (Closed)

module Categories.Rosen.TabEquivalence {o ℓ e} {C : Category o ℓ e} {M : Monoidal C} (Cl : Closed M) where

-- Equivalence between the total category (see TotalCategory.agda) and the
-- tabulator of MRS-Profunctor (see Tabulator.agda).

open Category C

open import Data.Product using (_,_; proj₁; proj₂; _×_)

open import Categories.Adjoint using (_⊣_)
open import Categories.Category.Construction.Arrow
open import Categories.Functor using (Functor)
open import Categories.Functor.Profunctor.Tabulator
open import Categories.Morphism.Reasoning as MR
open import Categories.NaturalTransformation using (ntHelper; _∘ᵥ_; _∘ʳ_) renaming (NaturalTransformation to NT)
open import Categories.Rosen.Core Cl
open import Categories.Rosen.ProElements Cl {F = MRS-Profunctor}
open import Categories.Rosen.TotalCategory Cl using (tot⇒; total; [_,_∥_,_])

open Closed Cl using ([-,-]; [_,_]₀; [_,-]; [_,_]₁)
open HomReasoning
open MR


-- Eq: functor from the total category to the tabulator (identity on objects).
Eq : Functor total (Tabulator MRS-Profunctor) 
Eq = record
  { F₀ = λ x → x
  ; F₁ = λ { {x} {y} f →
      let module x = tab₀ x
          module y = tab₀ y
          module f = tot⇒ f
          module Φ = NT (MR2.Φ x.ξ)
          module l*ψ = NT ((nHom f.l ∘ʳ Cod) ∘ᵥ MR2.Φ y.ξ)
      in
      f.l , f.r ∥
        ( (begin
             f.r ∘ MR2.f x.ξ ∘ id   ≈⟨ refl⟩∘⟨ identityʳ ⟩
             f.r ∘ MR2.f x.ξ        ≈⟨ f.eqf ⟩
             MR2.f y.ξ ∘ f.l        ≈⟨ Equiv.sym identityˡ ⟩
             id ∘ (MR2.f y.ξ ∘ f.l) ∎)
        , (λ {t} →
            begin
              NT.η ((nHom id ∘ʳ Cod) ∘ᵥ MR2.Φ x.ξ) t ≈⟨ elimˡ C [-,-].identity ⟩
              Φ.η t                                  ≈⟨ Equiv.sym (f.eqΦ {t = t}) ⟩
              l*ψ.η t                                ∎)) }
  ; identity = Equiv.refl , Equiv.refl
  ; homomorphism = Equiv.refl , Equiv.refl
  ; F-resp-≈ = λ x → x
  }

-- Eq⁻¹: functor from the tabulator to the total category (identity on objects).
Eq⁻¹ : Functor (Tabulator MRS-Profunctor) total 
Eq⁻¹ = record
  { F₀ = λ x → x
  ; F₁ = λ { {x} {y} f →
      let module x  = tab₀ x
          module y  = tab₀ y
          module f  = tab⇒ f
          module Φ  = NT (MR2.Φ x.ξ)
          module l*ψ = NT ((nHom f.l ∘ʳ Cod) ∘ᵥ MR2.Φ y.ξ)
          eqf =
            let eqf' = proj₁ f.eq in
            begin
              f.r ∘ MR2.f x.ξ        ≈⟨ refl⟩∘⟨ Equiv.sym identityʳ ⟩
              f.r ∘ MR2.f x.ξ ∘ id   ≈⟨ eqf' ○ identityˡ ⟩
              MR2.f y.ξ ∘ f.l        ∎
          eqΦ = proj₂ f.eq
      in
      [ f.l , f.r
      ∥ eqf
      , (λ {s} {t} α →
          let r = Arr.Morphism⇒.cod⇒ α
              eqΦt : l*ψ.η t ≈ Φ.η t
              eqΦt = begin l*ψ.η t ≈⟨ Equiv.sym eqΦ ⟩ 
                           [ id , id ]₁ ∘ Φ.η t ≈⟨ (elimˡ C [-,-].identity) ⟩ 
                           Φ.η t ∎
          in eqΦt ⟩∘⟨refl ○ Φ.commute α) ] }
  ; identity = Equiv.refl , Equiv.refl
  ; homomorphism = Equiv.refl , Equiv.refl
  ; F-resp-≈ = λ x → x
  }


-- Surprise motherfucker: the tabulator and total are equivalent categories!!!
-- at first, it seems `total` is imposing a stronger condition, but in the end naturality of Φ allows to deduce it from first principles.
-- Eq⊣Eq⁻¹: adjoint equivalence proving the total category ≅ the tabulator.
Eq⊣Eq⁻¹ : Eq ⊣ Eq⁻¹
Eq⊣Eq⁻¹ = record
  { unit = ntHelper (record
    { η = λ _ → Category.id total
    ; commute = λ f → (id-comm-sym C , id-comm-sym C)
    })
  ; counit = ntHelper (record
    { η = λ _ → Category.id (Tabulator MRS-Profunctor)
    ; commute = λ f → (id-comm-sym C , id-comm-sym C)
    })
  ; zig = identity² , identity²
  ; zag = identity² , identity²
  }
