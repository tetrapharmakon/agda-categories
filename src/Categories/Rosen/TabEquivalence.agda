{-# OPTIONS --without-K --safe --warning=noUserWarning --warning=noUselessPrivate #-}

open import Level using (_⊔_)

open import Data.Product using (_,_; proj₁; proj₂; _×_)

open import Categories.Category using (Category)
open import Categories.Category.Construction.Arrow
open import Categories.Category.Monoidal using (Monoidal)
open import Categories.Category.Monoidal.Closed using (Closed)
open import Categories.Functor using (Functor)
open import Categories.NaturalTransformation using (ntHelper; _∘ᵥ_; _∘ʳ_) renaming (NaturalTransformation to NT)
open import Categories.Adjoint using (_⊣_)

module Categories.Rosen.TabEquivalence {o ℓ e} {C : Category o ℓ e} {M : Monoidal C} (Cl : Closed M) where

private
  module 𝒞 = Category C

open 𝒞

open Closed Cl using ([-,-]; [_,_]₀; [_,-]; [_,_]₁)

import Categories.Morphism.Reasoning as MR
open HomReasoning
open MR

open import Categories.Rosen.Core Cl
open import Categories.Rosen.TotalCategory Cl using (tot⇒; total; [_,_∥_,_])
open import Categories.Rosen.ProElements Cl {F = MRS-Profunctor}

open import Categories.Functor.Profunctor.Tabulator


Eq : Functor total (Tabulator MRS-Profunctor) 
Eq = record
  { F₀ = λ x → x
  ; F₁ = λ { {x} {y} f →
      let module x = tab₀ x
          module y = tab₀ y
          module f = tot⇒ f
          module ϕ = NT (MR2.ϕ x.ξ)
          module l*ψ = NT ((nHom f.l ∘ʳ Cod) ∘ᵥ MR2.ϕ y.ξ)
      in
      f.l , f.r ∥
        ( (begin
             f.r ∘ MR2.f x.ξ ∘ id   ≈⟨ refl⟩∘⟨ identityʳ ⟩
             f.r ∘ MR2.f x.ξ        ≈⟨ f.eqf ⟩
             MR2.f y.ξ ∘ f.l        ≈⟨ Equiv.sym identityˡ ⟩
             id ∘ (MR2.f y.ξ ∘ f.l) ∎)
        , (λ {t} →
            begin
              NT.η ((nHom id ∘ʳ Cod) ∘ᵥ MR2.ϕ x.ξ) t ≈⟨ elimˡ C [-,-].identity ⟩
              ϕ.η t                                  ≈⟨ Equiv.sym (f.eqϕ {t = t}) ⟩
              l*ψ.η t                                ∎)) }
  ; identity = Equiv.refl , Equiv.refl
  ; homomorphism = Equiv.refl , Equiv.refl
  ; F-resp-≈ = λ x → x
  }

Eq⁻¹ : Functor (Tabulator MRS-Profunctor) total 
Eq⁻¹ = record
  { F₀ = λ x → x
  ; F₁ = λ { {x} {y} f →
      let module x  = tab₀ x
          module y  = tab₀ y
          module f  = tab⇒ f
          module ϕ  = NT (MR2.ϕ x.ξ)
          module l*ψ = NT ((nHom f.l ∘ʳ Cod) ∘ᵥ MR2.ϕ y.ξ)
          eqf =
            let eqf' = proj₁ f.eq in
            begin
              f.r ∘ MR2.f x.ξ        ≈⟨ refl⟩∘⟨ Equiv.sym identityʳ ⟩
              f.r ∘ MR2.f x.ξ ∘ id   ≈⟨ eqf' ○ identityˡ ⟩
              MR2.f y.ξ ∘ f.l        ∎
          eqϕ = proj₂ f.eq
      in
      [ f.l , f.r
      ∥ eqf
      , (λ {s} {t} α →
          let r = Arr.Morphism⇒.cod⇒ α
              eqϕt : l*ψ.η t ≈ ϕ.η t
              eqϕt = begin l*ψ.η t ≈⟨ Equiv.sym eqϕ ⟩ 
                           [ id , id ]₁ ∘ ϕ.η t ≈⟨ (elimˡ C [-,-].identity) ⟩ 
                           ϕ.η t ∎
          in eqϕt ⟩∘⟨refl ○ ϕ.commute α) ] }
  ; identity = Equiv.refl , Equiv.refl
  ; homomorphism = Equiv.refl , Equiv.refl
  ; F-resp-≈ = λ x → x
  }


-- Surprise motherfucker: the tabulator and total are equivalent categories!!!
-- at first, it seems `total` is imposing a stronger condition, but in the end naturality of ϕ allows to deduce it from first principles.
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


-- open import Categories.Rosen.Tabulator Cl using (V₁;𝕋MRS)
-- sending an arrow h : A ⇒ B to the MR system
-- (h, const) exists only on a Cartesian ambient category C
-- 𝕀 : Functor Arr.Arrow 𝕋MRS 
-- 𝕀 = record
--   { F₀ = λ {record { dom = dom ; cod = cod ; arr = a } → 
--        (dom , cod) 
--        ∣ ⟪ a , {!  !} ⟫}
--   ; F₁ = {!  !}
--   ; identity = {!  !}
--   ; homomorphism = {!  !}
--   ; F-resp-≈ = {!  !}
--   }