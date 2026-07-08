{-# OPTIONS --without-K --safe --warning=noUserWarning --warning=noUselessPrivate #-}

open import Level using (_⊔_)
open import Categories.Category using (Category)
open import Categories.Category.Monoidal using (Monoidal)
open import Categories.Category.Monoidal.Closed using (Closed)

module Categories.Rosen.Adjunction.TotRep {o ℓ e} {C : Category o ℓ e} {M : Monoidal C} (Cl : Closed M) where

open Category C

open import Data.Product using (_,_; proj₁; proj₂; _×_)

open import Categories.Adjoint using (_⊣_)
open import Categories.Category.Construction.Arrow
open import Categories.Functor using (Functor)
open import Categories.Functor.Profunctor.Tabulator
open import Categories.Morphism.Reasoning as MR
open import Categories.NaturalTransformation using (ntHelper; _∘ᵥ_; _∘ʳ_) renaming (NaturalTransformation to NT)
open import Categories.Rosen.Core Cl
open import Categories.Rosen.Repairs Cl
open import Categories.Rosen.TotalCategory Cl using (tot⇒; total; [_,_∥_,_])
open import Categories.Rosen.ProElements Cl {F = MRS-Profunctor}

open Closed Cl using ([-,-]; [_,_]₀; [_,-]; [_,_]₁)
open HomReasoning
open MR


-- The coreflector of total on the category of repairs
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

-- the inclusion of repairs in total
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

-- J and K are adjoint 
𝕁⊣K : 𝕁 ⊣ K 
-- note that J is full and faithful (unit is id)
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