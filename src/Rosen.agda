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

module Rosen {o ℓ e} {C : Category o ℓ e} {M : Monoidal C} (Cl : Closed M) where

private
  module 𝒞 = Category C

open 𝒞

open Closed Cl using ([-,-]; [_,_]₀; [_,-]; [_,_]₁; Hom[-⊗_,-]; Hom[-,[_,-]]; Hom-NI)

module Arr = Categories.Category.Construction.Arrow C

-- Codomain functor Arrow(C) → C.
Cod : Functor Arr.Arrow C
Cod = record
  { F₀           = Arr.Morphism.cod
  ; F₁           = Arr.Morphism⇒.cod⇒
  ; identity     = Equiv.refl
  ; homomorphism = Equiv.refl
  ; F-resp-≈     = λ eq → proj₂ eq
  }

record MR2 (A B : Obj) : Set (o ⊔ ℓ ⊔ e) where
  eta-equality
  constructor ⟪_,_⟫
  field
    f : A ⇒ B
    ϕ : NaturalTransformation Cod (([_,-] A) ∘F Cod)

  ϕη = NaturalTransformation.η ϕ
  ϕcommute = λ {X Y : Category.Obj Arr.Arrow} t → NaturalTransformation.commute ϕ {X} {Y} t
  ϕf = ϕη (record { arr = f }) ∘ f
  -- ϕ[ϕf] = {!  !}

MR2-Setoid : Obj → Obj → Setoid (o ⊔ ℓ ⊔ e) (o ⊔ ℓ ⊔ e)
MR2-Setoid A B = record
  { Carrier = MR2 A B
  ; _≈_ = λ (⟪ f , ϕ ⟫) (⟪ g , ϕ' ⟫) → (f ≈ g) × (ϕ ≃ ϕ')
  ; isEquivalence = record 
    { refl = Equiv.refl , (λ {x₁} → Equiv.refl) 
    ; sym = λ (pf , k) → Equiv.sym pf , Equiv.sym k 
    ; trans = λ (pf₁ , h) (pf₂ , k) → Equiv.trans pf₁ pf₂ , Equiv.trans h k
    } 
  }


nHom : ∀ {A B} → A ⇒ B → NaturalTransformation ([_,-] B) ([_,-] A)
nHom {A} {B} f = record 
  { η = λ X → [ f , id ]₁ 
  ; commute = λ h → Equiv.sym [ [-,-] ]-commute
  ; sym-commute = λ h → [ [-,-] ]-commute
  }


open import Categories.NaturalTransformation renaming (id to idN)
open import Categories.NaturalTransformation.NaturalIsomorphism
  using (niHelper)
  
nHom-identity : ∀ {A} → nHom (id {A}) ≃ idN
nHom-identity = {!  !}

open import Categories.Category.Instance.Sets

MRS-SetP : Bifunctor (Category.op C) C (Sets (o ⊔ ℓ ⊔ e))
MRS-SetP = record
  { F₀ = λ {(A , B) → MR2 A B}
  ; F₁ = λ { {(A , B)} {(A' , B')} (u , v) ⟪ f , ϕ ⟫ → let module ϕ = NaturalTransformation ϕ in
    ⟪ v ∘ f ∘ u , (nHom u ∘ʳ Cod) ∘ᵥ ϕ ⟫}
  ; identity = {!  !}
  ; homomorphism = {!  !}
  ; F-resp-≈ = {!  !}
  }

open import Categories.Category.Construction.Elements using (Elements)

𝓔MRS = Elements MRS-SetP

import Categories.Morphism.Reasoning as MR

open HomReasoning 
open MR
-- Type of the desired profunctor C.op × C → Sets sending (A , B) ↦ MR2 A B.
MRS-Profunctor : Bifunctor (Category.op C) C (Setoids (o ⊔ ℓ ⊔ e) (o ⊔ ℓ ⊔ e))
MRS-Profunctor = record
  { F₀ = λ { (A , B) → MR2-Setoid A B }
  ; F₁ = λ { {(A , B)} {(A' , B')} (u , v) → record 
    { _⟨$⟩_ = λ {⟪ f , ϕ ⟫ → ⟪ v ∘ f ∘ u , (nHom u ∘ʳ Cod) ∘ᵥ ϕ ⟫ }
    ; cong = λ { {⟪ f , ϕ ⟫} {⟪ g , ϕ' ⟫} (f≈g , ϕ≈ϕ') →
        (∘-resp-≈ Equiv.refl (∘-resp-≈ f≈g Equiv.refl))
      , (λ {x} → ∘-resp-≈ʳ (ϕ≈ϕ' {x}))
      }
    }}
  ; identity = λ { {(A , B)} {⟪ f , ϕ ⟫} {⟪ g , ϕ' ⟫} →
      let module Hom = Functor [-,-] in
      let module CodF = Functor Cod in
        ( λ (f≈g , ϕ≈ϕ') → (begin id ∘ f ∘ id ≈⟨ identityˡ ⟩ 
                                  f ∘ id      ≈⟨ identityʳ ⟩ 
                                  f           ≈⟨ f≈g ⟩ 
                                  g           ∎) 
        , λ { {h} →
            let module ϕ = NaturalTransformation ϕ
                module ϕ' = NaturalTransformation ϕ'
            in
            begin
              [ id , id ]₁ ∘ ϕ.η h ≈⟨ ∘-resp-≈ Hom.identity Equiv.refl ⟩
              id ∘ ϕ.η h           ≈⟨ identityˡ ⟩
              ϕ.η h                ≈⟨ ϕ≈ϕ' {h} ⟩
              ϕ'.η h               ∎ })
     }
  ; homomorphism = λ { {(A , B)} {(A' , B')} {(A'' , B'')} {f = (u₁ , v₁)} {g = (u₂ , v₂)} {⟪ f , ϕ ⟫} {⟪ g , ϕ' ⟫} →
       let module Hom = Functor [-,-] 
           module Hom[1-] {A} = Functor (appˡ [-,-] A) 
           module Hom[-1] {A} = Functor (appʳ [-,-] A) in
         ( λ { (f≈g , ϕ≈ϕ') → 
             (begin (v₂ ∘ v₁) ∘ f ∘ u₁ ∘ u₂     ≈˘⟨ assoc ○ assoc ⟩ 
                    (((v₂ ∘ v₁) ∘ f) ∘ u₁) ∘ u₂ ≈⟨ (refl⟩∘⟨ f≈g) ⟩∘⟨refl ⟩∘⟨refl ⟩ 
                    (((v₂ ∘ v₁) ∘ g) ∘ u₁) ∘ u₂ ≈⟨ (assoc ⟩∘⟨refl) ○ (assoc ⟩∘⟨refl) ⟩ 
                    (v₂ ∘ (v₁ ∘ (g ∘ u₁))) ∘ u₂ ≈⟨ assoc ○ sym-assoc ○ assoc ⟩ 
                    v₂ ∘ (v₁ ∘ g ∘ u₁) ∘ u₂     ∎)
        , λ { {h} →
            let module ϕ = NaturalTransformation ϕ
                module ϕ' = NaturalTransformation ϕ'
            in
            begin
              [ u₁ ∘ u₂ , id ]₁ ∘ ϕ.η h              ≈⟨ ∘-resp-≈ Equiv.refl (ϕ≈ϕ' {h}) ⟩
              [ u₁ ∘ u₂ , id ]₁ ∘ ϕ'.η h             ≈⟨ Hom[-1].homomorphism ⟩∘⟨refl ⟩
              ([ u₂ , id ]₁ ∘ [ u₁ , id ]₁) ∘ ϕ'.η h ≈⟨ assoc ⟩
              [ u₂ , id ]₁ ∘ ([ u₁ , id ]₁ ∘ ϕ'.η h) ∎ } })
     }
  ; F-resp-≈ = λ { {(A , B)} {(A' , B')} {f = (u , v)} {g = (u' , v')} (u≈u' , v≈v') {⟪ f , ϕ ⟫} {⟪ g , ϕ' ⟫} →
       let module Hom = Functor [-,-] in 
         ( λ { (f≈g , ϕ≈ϕ') → 
           (begin v ∘ f ∘ u   ≈⟨ ∘-resp-≈ v≈v' (∘-resp-≈ʳ u≈u') ⟩ 
                  v' ∘ f ∘ u' ≈⟨ refl⟩∘⟨ f≈g ⟩∘⟨refl ⟩
                  v' ∘ g ∘ u' ∎) 
        , λ { {h} →
            let module ϕ = NaturalTransformation ϕ
                module ϕ' = NaturalTransformation ϕ'
            in
            begin
              [ u , id ]₁ ∘ ϕ.η h   ≈⟨ ∘-resp-≈ʳ (ϕ≈ϕ' {h}) ⟩
              [ u , id ]₁ ∘ ϕ'.η h  ≈⟨ ∘-resp-≈ˡ (Hom.F-resp-≈ (u≈u' , Equiv.refl)) ⟩
              [ u' , id ]₁ ∘ ϕ'.η h ∎ } })
     }
  }


open import Categories.Functor.Profunctor.Tabulator
module _ where
  
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

  total : Category (o ⊔ ℓ ⊔ e) (o ⊔ ℓ ⊔ e) {!  !} 
  total = record
    { Obj = tab₀ MRS-Profunctor
    ; _⇒_ = λ s t → tot⇒ s t
    ; _≈_ = λ h k → tot⇒.l h ≈ tot⇒.l k × tot⇒.r h ≈ tot⇒.r k
    ; id = λ { {(A , B) ∣ ⟪ f , ϕ ⟫} → 
         [ id , id 
         ∥ id-comm-sym C , 
         (begin {!  !} ≈⟨ identityʳ ⟩ 
                {!  !} ≈⟨ {!  !} ⟩ 
                {!  !} ≈⟨ {!  !} ⟩ 
                {!  !} ∎) 
         ]}
    ; _∘_ = λ {t t' → let module t = tot⇒ t
                          module t' = tot⇒ t'
                      in [ t.l ∘ t'.l , t.r ∘ t'.r ∥ 
                           {!  !} 
                         , {!  !} 
                         ]}
    ; assoc = assoc , {!  !}
    ; sym-assoc = sym-assoc , {!  !}
    ; identityˡ = identityˡ , {!  !}
    ; identityʳ = identityʳ , {!  !}
    ; identity² = identity² , {!  !}
    ; equiv = {!  !}
    ; ∘-resp-≈ = {!  !}
    }

open import Categories.Functor.Construction.LiftSetoids using (LiftSetoids)

𝕋MRS = Tabulator MRS-Profunctor

π  = projection {p = MRS-Profunctor}
þ  = cell {p = MRS-Profunctor}

-- gives f
V₁ : Functor 𝕋MRS Arr.Arrow
V₁ = record
  { F₀ = λ { ((A , B) ∣ ξ) → record { arr = MR2.f ξ } }
  ; F₁ = λ { {(A , B) ∣ ⟪ f , ϕ ⟫} {(A' , B') ∣ ⟪ g , ϕ' ⟫} (l , r ∥ eq) → mor⇒ {dom⇒ = l} {cod⇒ = r} 
    (begin r ∘ f      ≈˘⟨ refl⟩∘⟨ identityʳ ⟩ 
           r ∘ f ∘ id ≈⟨ (proj₁ eq) ○ identityˡ ⟩
           g ∘ l      ∎) }
  ; identity = 
      Equiv.refl 
    , Equiv.refl
  ; homomorphism = 
      Equiv.refl 
    , Equiv.refl
  ; F-resp-≈ = λ { x → x }
  }

-- Object part of the would-be “nabla” map:
-- it sends (A , B ∣ ⟪ f , ϕ ⟫) to the arrow B → [ A , B ] given by ϕ at f.
--
-- This does not extend to a functor 𝕋MRS → Arrow(C) in general: a morphism
-- (l , r ∥ eq) has l : A ⇒ A′, but functoriality would require a canonical
-- morphism [ A , B ] ⇒ [ A′ , B′ ], and [-,-] is contravariant in its first
-- argument (so it wants A′ ⇒ A instead).
-- ∇₀ : (𝕋MRS .Obj) → Arr.Arrow .Obj
-- ∇₀ ((A , B) ∣ ξ) =
--   let module phi = NaturalTransformation (MR2.ϕ ξ) in
--   record { arr = phi.η (record { arr = MR2.f ξ }) }

∇ : Functor 𝕋MRS Arr.Arrow
∇ = record
  { F₀ = λ ((A , B) ∣ ξ) → 
  let module phi = NaturalTransformation (MR2.ϕ ξ) in
  record { arr = phi.η (record { arr = MR2.f ξ }) }
  ; F₁ = λ { {(A , B) ∣ ⟪ f , ϕ ⟫} {(A' , B') ∣ ⟪ g , ψ ⟫} (l , r ∥ eq) → mor⇒ (begin {!  !} ≈⟨ {!  !} ⟩ 
              {!  !} ≈⟨ {!  !} ⟩ 
              {!  !} ∎)}
  ; identity = {!  !}
  ; homomorphism = {!  !}
  ; F-resp-≈ = {!  !}
  }

ϵ  : NaturalTransformation MRS-Profunctor (LiftSetoids (o ⊔ e) (o ⊔ ℓ) ∘F Hom[ C ][-,-])
ϵ = ntHelper record 
  { η = λ { (A , B) → record 
    { _⟨$⟩_ = λ {⟪ f , ϕ ⟫ → lift f }
    ; cong = λ { {⟪ f , ϕ ⟫} {⟪ g , ϕ' ⟫} eq → lift (proj₁ eq) }
    } }
  ; commute = λ { {(A , B)} {(A' , B')} (u , v) {⟪ f , ϕ ⟫} {⟪ g , ϕ' ⟫} eq →
      lift (∘-resp-≈ʳ (∘-resp-≈ˡ (proj₁ eq))) }
  }

{-
∇ : Functor 𝓔MRS Arr.Arrow
∇ = record
  { F₀ = λ {((A , B) , ξ) → record { arr = MR2.ϕf ξ }}
  ; F₁ = λ { {(A , B) , X@(⟪ f , ϕ ⟫)} {(A' , B') , Y@(⟪ g , ψ ⟫)} ((l , r) , q) → 
      mor⇒ (begin [ l , r ]₁ ∘ MR2.ϕf X ≈⟨  {!  !} ⟩ 
                  {!  !} ≈⟨  {!  !} ⟩ 
                  MR2.ϕf Y ∘ {!  !} ∎) }
  ; identity = {!  !}
  ; homomorphism = {!  !}
  ; F-resp-≈ = {!  !}
  }
-- here be the pullback of two functors, V₁ and Cod. 
-}