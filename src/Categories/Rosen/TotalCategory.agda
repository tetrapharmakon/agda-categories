{-# OPTIONS --without-K --safe --warning=noUserWarning --warning=noUselessPrivate #-}

open import Level using (_⊔_;lift;lower;zero;suc)

open import Data.Product using (_,_; proj₁; proj₂; _×_)
open import Relation.Binary using (IsEquivalence)
open import Relation.Binary.Bundles using (Setoid)

open import Categories.Category using (Category)
open import Categories.Category.Construction.Arrow
open import Categories.Category.Instance.Setoids
open import Categories.Category.Monoidal using (Monoidal)
open import Categories.Category.Monoidal.Closed using (Closed)
open import Categories.Functor using (Functor; _∘F_)
open import Categories.Functor.Bifunctor using (Bifunctor; appˡ; appʳ)
open import Categories.Functor.Bifunctor.Properties using ([_]-commute)
open import Categories.NaturalTransformation using (NaturalTransformation;_∘ᵥ_; _∘ₕ_; _∘ˡ_; _∘ʳ_)
open import Categories.NaturalTransformation.Equivalence using (_≃_; ≃-isEquivalence)

open import Categories.Functor.Hom using (Hom[_][-,-]; Hom[_][_,_])
module Categories.Rosen.TotalCategory {o ℓ e} {C : Category o ℓ e} {M : Monoidal C} (Cl : Closed M) where

private
  module 𝒞 = Category C

open 𝒞

open Closed Cl using ([-,-]; [_,_]₀; [_,-]; [_,_]₁; Hom[-⊗_,-]; Hom[-,[_,-]]; Hom-NI)

import Categories.Morphism.Reasoning as MR
open HomReasoning 
open MR

open import Categories.Rosen.Core Cl
open import Categories.Functor.Profunctor.Tabulator

record tot⇒ (x y : tab₀ MRS-Profunctor) : Set (o ⊔ ℓ ⊔ e) where
  constructor [_,_∥_,_]
  module x = tab₀ x
  module y = tab₀ y
  field
    l : x.L ⇒ y.L 
    r : x.R ⇒ y.R 
  
  f = MR2.f x.ξ
  g = MR2.f y.ξ

  module ϕ = NaturalTransformation (MR2.ϕ x.ξ)
  module l*ψ = NaturalTransformation ((nHom l ∘ʳ Cod) ∘ᵥ MR2.ϕ y.ξ)
  
  field
    eqf : r ∘ f ≈ g ∘ l
    eqϕ : l*ψ.η (record { arr = g }) ∘ r ≈ Functor.F₁ [ x.L ,-] r ∘ ϕ.η (record { arr = f })

total : Category (o ⊔ ℓ ⊔ e) (o ⊔ ℓ ⊔ e) e
total = record
  { Obj = tab₀ MRS-Profunctor
  ; _⇒_ = λ s t → tot⇒ s t
  ; _≈_ = λ h k → tot⇒.l h ≈ tot⇒.l k × tot⇒.r h ≈ tot⇒.r k
  ; id = λ { {(A , B) ∣ ⟪ f , ϕ ⟫} → 
       let module ϕNT = NaturalTransformation ϕ
           module l*ϕ = NaturalTransformation ((nHom id ∘ʳ Cod) ∘ᵥ ϕ)
       in
       [ id , id
       ∥ id-comm-sym C
       , (begin
            l*ϕ.η (record { arr = f }) ∘ id
              ≈⟨ identityʳ ⟩
            l*ϕ.η (record { arr = f })
              ≈⟨ Equiv.refl ⟩
            Functor.F₁ [ A ,-] id ∘ ϕNT.η (record { arr = f })
          ∎)
       ]}
  ; _∘_ = λ {t t' → let module t = tot⇒ t
                        module t' = tot⇒ t'
                     in [ t.l ∘ t'.l , t.r ∘ t'.r ∥ 
                          (begin (t.r ∘ t'.r) ∘ t'.f ≈⟨ pullʳ C t'.eqf ⟩ 
                                 t.r ∘ MR2.f t'.y.ξ ∘ t'.l ≈⟨ pullˡ C t.eqf ⟩ 
                                 (MR2.f t.y.ξ ∘ t.l) ∘ t'.l ≈⟨ assoc ⟩ 
                                 MR2.f t.y.ξ ∘ t.l ∘ t'.l ∎) 
                        , (let module Hx = Functor [ t'.x.L ,-]
                               module Hy = Functor [ t.x.L ,-]
                               module ψ = NaturalTransformation (MR2.ϕ t.y.ξ)
                               ψ₁ = ψ.η (record { arr = t.g })
                               ϕ₁ = t.ϕ.η (record { arr = t.f })
                               ϕ'₁ = t'.ϕ.η (record { arr = t'.f })
                               module Hom[-1] {X} = Functor (appʳ [-,-] X)
                           in
                           begin
                             ([ t.l ∘ t'.l , id ]₁ ∘ ψ₁) ∘ (t.r ∘ t'.r)             ≈⟨ ∘-resp-≈ (∘-resp-≈ (Hom[-1].homomorphism {f = t.l} {g = t'.l}) Equiv.refl) Equiv.refl ⟩
                             (([ t'.l , id ]₁ ∘ [ t.l , id ]₁) ∘ ψ₁) ∘ (t.r ∘ t'.r) ≈⟨ ∘-resp-≈ assoc Equiv.refl ⟩
                             ([ t'.l , id ]₁ ∘ ([ t.l , id ]₁ ∘ ψ₁)) ∘ (t.r ∘ t'.r) ≈˘⟨ assoc ⟩
                             (([ t'.l , id ]₁ ∘ ([ t.l , id ]₁ ∘ ψ₁)) ∘ t.r) ∘ t'.r ≈⟨ ∘-resp-≈ assoc Equiv.refl ⟩
                             ([ t'.l , id ]₁ ∘ (([ t.l , id ]₁ ∘ ψ₁) ∘ t.r)) ∘ t'.r ≈⟨ ∘-resp-≈ (∘-resp-≈ Equiv.refl t.eqϕ) Equiv.refl ⟩
                             ([ t'.l , id ]₁ ∘ (Hy.F₁ t.r ∘ ϕ₁)) ∘ t'.r             ≈⟨ ∘-resp-≈ (Equiv.sym assoc) Equiv.refl ⟩
                             (([ t'.l , id ]₁ ∘ Hy.F₁ t.r) ∘ ϕ₁) ∘ t'.r             ≈⟨ ∘-resp-≈ (∘-resp-≈ (Equiv.sym [ [-,-] ]-commute) Equiv.refl) Equiv.refl ⟩
                             ((Hx.F₁ t.r ∘ [ t'.l , id ]₁) ∘ ϕ₁) ∘ t'.r             ≈⟨ ∘-resp-≈ assoc Equiv.refl ⟩
                             (Hx.F₁ t.r ∘ ([ t'.l , id ]₁ ∘ ϕ₁)) ∘ t'.r             ≈⟨ assoc ⟩
                             Hx.F₁ t.r ∘ (([ t'.l , id ]₁ ∘ ϕ₁) ∘ t'.r)             ≈⟨ ∘-resp-≈ Equiv.refl t'.eqϕ ⟩
                             Hx.F₁ t.r ∘ (Hx.F₁ t'.r ∘ ϕ'₁)                         ≈˘⟨ assoc ⟩
                             (Hx.F₁ t.r ∘ Hx.F₁ t'.r) ∘ ϕ'₁                         ≈⟨ ∘-resp-≈ (Equiv.sym Hx.homomorphism) Equiv.refl ⟩
                             Hx.F₁ (t.r ∘ t'.r) ∘ ϕ'₁                               ∎)
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

broken∇ : Functor total Arr.Arrow
broken∇ = record
  { F₀ = λ ((A , B) ∣ ξ) → 
  let module phi = NaturalTransformation (MR2.ϕ ξ) 
  in record { arr = phi.η (record { arr = MR2.f ξ }) }
  ; F₁ = λ { {(A , B) ∣ ⟪ f , ϕ ⟫} {(A' , B') ∣ ⟪ g , ψ ⟫} ([ l , r ∥ eqf , eqϕ ]) → 
          let module ϕ = NaturalTransformation ϕ
              module ψ = NaturalTransformation ψ
          in
          mor⇒ {dom⇒ = r} {cod⇒ = {! ? ∘ ψ.η (record { arr = g }) !} ∘ Functor.F₁ [ A ,-] r} (begin
            _ ∘ ϕ.η (record { arr = f }) ≈⟨ {! eqϕ !} ⟩
            {!  !}                       ≈⟨ {!  !} ⟩
            ψ.η (record { arr = g }) ∘ r
            ∎)}
  ; identity = Equiv.refl , {!  !}
  ; homomorphism = Equiv.refl , {!  !}
  ; F-resp-≈ = λ x → {!  !} , {!  !}
  }
