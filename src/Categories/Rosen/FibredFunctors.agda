{-# OPTIONS --without-K --safe --warning=noUserWarning --warning=noUselessPrivate #-}

open import Level using (_⊔_; lift; lower; zero; suc)

open import Data.Product using (_,_; proj₁; proj₂; _×_)

open import Categories.Category using (Category)
open import Categories.Category.Construction.Arrow
open import Categories.Category.Instance.Setoids
open import Categories.Category.Monoidal using (Monoidal)
open import Categories.Category.Monoidal.Closed using (Closed)
open import Categories.Functor using (Functor; _∘F_)
open import Categories.NaturalTransformation using (ntHelper; _∘ᵥ_; _∘ₕ_; _∘ˡ_; _∘ʳ_) renaming (NaturalTransformation to NT)
open import Categories.NaturalTransformation.Equivalence using (_≃_; ≃-isEquivalence)
open import Categories.Adjoint using (_⊣_)

module Categories.Rosen.FibredFunctors {o ℓ e} {C : Category o ℓ e} {M : Monoidal C} (Cl : Closed M) where

private
  module 𝒞 = Category C

open 𝒞

open Closed Cl using ([-,-]; [_,_]₀; [_,-]; [_,_]₁)

import Categories.Morphism.Reasoning as MR
open HomReasoning
open MR

open import Categories.Rosen.Core Cl
open import Categories.Rosen.TotalCategory Cl using (tot⇒; total; [_,_∥_,_])

open import Categories.Functor.Profunctor.Tabulator

-- This functor works.
K : Functor total repairs
K = record
  { F₀ = λ x → 
      let module x = tab₀ x
          module ξx = MR2 x.ξ 
      in record { A = x.L ; ϕ = ξx.ϕ }
  ; F₁ = λ { {x} {y} f → 
      let module x = tab₀ x
          module y = tab₀ y
          module f = tot⇒ f 
      in record { u = f.l ; eq = f.eqϕ } }
  ; identity = λ {A} → Equiv.refl
  ; homomorphism = Equiv.refl
  ; F-resp-≈ = proj₁
  }

-- Is there a functor in the opposite direction?
-- Clearly they can't be an equivalence
𝕁 : Functor repairs total 
𝕁 = record
  { F₀ = λ {(record { A = A ; ϕ = ϕ }) → (A , A) ∣ ⟪ id , ϕ ⟫}
  ; F₁ = λ { {X} {Y} f → let module f = rep⇒ f in
  [ f.u , f.u 
  ∥ id-comm C , (λ {s} {t} α →
      let module X₀ = rep₀ X
          module Y₀ = rep₀ Y
          module ϕX = NT X₀.ϕ
          module ϕY = NT Y₀.ϕ
          r = Arr.Morphism⇒.cod⇒ α
      in
      begin
        (NT.η ((nHom f.u ∘ʳ Cod) ∘ᵥ Y₀.ϕ) t) ∘ r                      ≈⟨ assoc ○ (refl⟩∘⟨ ϕY.commute α) ○ sym-assoc ⟩
        (NT.η (nHom f.u ∘ʳ Cod) t ∘ Functor.F₁ [ Y₀.A ,-] r) ∘ ϕY.η s ≈⟨ (∘-resp-≈ (NT.commute (nHom f.u ∘ʳ Cod) α) Equiv.refl) ○ assoc ⟩
        Functor.F₁ [ X₀.A ,-] r ∘ (NT.η (nHom f.u ∘ʳ Cod) s ∘ ϕY.η s) ≈⟨ refl⟩∘⟨ f.eq {x = s} ⟩
        Functor.F₁ [ X₀.A ,-] r ∘ ϕX.η s                              ∎) ]}
  ; identity = Equiv.refl , Equiv.refl
  ; homomorphism = Equiv.refl , Equiv.refl
  ; F-resp-≈ = λ x → x , x
  }

𝕁⊣K : 𝕁 ⊣ K -- J and K are adjoint 
-- J is full and faithful (unit is id)
𝕁⊣K = record 
 { unit = ntHelper (record 
   { η = λ {record { A = A ; ϕ = ϕ } → record 
      { u = id 
      ; eq =  elimˡ C [-,-].identity
      } }
    ; commute = λ f →
        let module f = rep⇒ f in
        begin
          id ∘ f.u ≈⟨ identityˡ ⟩
          f.u      ≈⟨ Equiv.sym identityʳ ⟩
          f.u ∘ id ∎ }) 
  ; counit = ntHelper (record 
    { η = λ {((L , R) ∣ ξ) → 
      [ id , MR2.f ξ 
      ∥ Equiv.refl 
     , (λ {s} {t} α →
           let module ϕ = NT (MR2.ϕ ξ)
               r = Arr.Morphism⇒.cod⇒ α
           in
           begin
             (([ id , id ]₁ ∘ ϕ.η t) ∘ r) ≈⟨ assoc ○ (elimˡ C [-,-].identity) ⟩
             ϕ.η t ∘ r                    ≈⟨ ϕ.commute α ⟩
             Functor.F₁ [ L ,-] r ∘ ϕ.η s ∎) ] }
    ; commute = λ f →
        let module f = tot⇒ f in
        ( Equiv.trans identityˡ (Equiv.sym identityʳ)
        , Equiv.sym f.eqf ) }) 
  ; zig = identity² , identity² 
  ; zag = λ {B} → identity² 
  }

-- Instead, one would like a functor tabulator -> repairs to define MR3 as pullback?

{-

tab(MRS-Profunctor) -----V₁----> C^→ <----?---- repairs <---∇---- total

probably this functor `?` does not exist...
It seems that the only way to define a pullback is done in 

https://github.com/tetrapharmakon/agda-categories/blob/5b97012b94ad174962a136951e9ab9e73d7cbcb0/src/Categories/Rosen/FibreA.agda#L145

where the "basepoint" A is taken into consideration.
-}

-- Q : Functor repairs Arr.Arrow
-- Q = record
--   { F₀ = λ x → let module x = rep₀ x in (record { arr = NT.η x.ϕ (record { arr = id }) })
--   ; F₁ = λ { {x} {y} f → 
--     let module x = rep₀ x 
--         module y = rep₀ y
--         module f = rep⇒ f
--     in mor⇒ {!  !}}
--   ; identity = {!  !}
--   ; homomorphism = {!  !}
--   ; F-resp-≈ = {!  !}
--   }



-- total is a subcategory of the tabulator.
-- it would be nice to invoke the adjoint functor theorem to prove that the inclusion has an adjoint, giving the "universal" (free or cofree) compatible object of the tabulator, universally imposing the equation `nat` on morphisms


incl : Functor total (Tabulator MRS-Profunctor) 
incl = record
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

forse : Functor (Tabulator MRS-Profunctor) total 
forse = record
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
              eqϕt = Equiv.trans (Equiv.sym (eqϕ {x = t})) (elimˡ C [-,-].identity)
          in eqϕt ⟩∘⟨refl ○ ϕ.commute α) ] }
  ; identity = Equiv.refl , Equiv.refl
  ; homomorphism = Equiv.refl , Equiv.refl
  ; F-resp-≈ = λ x → x
  }


-- Surprise motherfucker: the tabulator and total are equivalent categories!!!
-- at first, it seems `total` is imposing a stronger condition, but in the end naturality of ϕ allows to deduce it from first principles.
incl⊣forse : incl ⊣ forse
incl⊣forse = record
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
