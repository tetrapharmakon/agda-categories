{-# OPTIONS --without-K --warning=noUserWarning --warning=noUselessPrivate --warning=noUnsupportedIndexedMatch #-}

open import Categories.Category using (Category)
open import Categories.Category.Monoidal using (Monoidal)
open import Categories.Category.Monoidal.Closed using (Closed)
open import Level using (_⊔_)

module Categories.Rosen.Coherent.Core {o ℓ e} {C : Category o ℓ e} {M : Monoidal C} (Cl : Closed M) where

-- Core definitions for the category of (M,R)-systems.
-- Exports: Cod, nHom, nHom-identity, MR2, MR2-Setoid, MRS-Profunctor.

open import Data.Product using (_,_; proj₁; proj₂; _×_)
open import Relation.Binary.Bundles using (Setoid)

open import Categories.Category.Construction.Arrow
open import Categories.Category.Instance.Setoids using (Setoids)
open import Categories.Functor using (Functor; _∘F_) renaming (id to idF)
open import Categories.Functor.Bifunctor using (Bifunctor; appˡ; appʳ)
open import Categories.Functor.Bifunctor.Properties using ([_]-commute)
open import Categories.Morphism.Reasoning as MR
open import Categories.NaturalTransformation using (NaturalTransformation;ntHelper; _∘ᵥ_; _∘ₕ_; _∘ˡ_; _∘ʳ_) renaming (id to idN)
open import Categories.NaturalTransformation.Equivalence using (_≃_)

import Reason
open Reason C

open Closed Cl using (adjoint; unitorˡ;unitorʳ-commute-to; unitorʳ-commute-from;unitorʳ; [-,-]; unit; [_,_]₀; [_,-]; [-,_]; [_,_]₁; _⊗₁_)

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
  constructor ⟪_,_⟫
  field
    f : A ⇒ B
    Φ : NaturalTransformation Cod (([_,-] A) ∘F Cod)

  Φη = NaturalTransformation.η Φ
  Φη₀ = Φη (record { arr = f })
  Φcommute = λ {X Y : Category.Obj Arr.Arrow} t → NaturalTransformation.commute Φ {X} {Y} t

-- MR2 as a Setoid: two MR2 elements are equal when their f components are equal
-- and their Φ components are ≃-equal.
MR2-Setoid : Obj → Obj → Setoid (o ⊔ ℓ ⊔ e) (o ⊔ ℓ ⊔ e)
MR2-Setoid A B = record
  { Carrier = MR2 A B
  ; _≈_ = λ (⟪ f , Φ ⟫) (⟪ g , Φ' ⟫) → (f ≈ g) × (Φ ≃ Φ')
  ; isEquivalence = record
    { refl = Equiv.refl , (λ {x₁} → Equiv.refl)
    ; sym = λ (pf , k) → Equiv.sym pf , Equiv.sym k
    ; trans = λ (pf₁ , h) (pf₂ , k) → Equiv.trans pf₁ pf₂ , Equiv.trans h k
    }
  }

{-
  X -- u --> Y 
  |          |
u |  u ⇒ id  |
  V          |
  Y -------- Y
-}
u⇒1 : ∀ {X Y} (u : X ⇒ Y) → Morphism⇒ C (record {arr = u}) (record {arr = id {Y}})
u⇒1 u = mor⇒ {dom⇒ = u} {cod⇒ = id} refl

{-
X -------- X 
|          |
|  id ⇒ u  | u
|          V
X ---u---> Y
-}
1⇒u : ∀ {X Y} (u : X ⇒ Y) → Morphism⇒ C (record { arr = id {X} }) (record {arr = u})
1⇒u u = mor⇒ {dom⇒ = id} {cod⇒ = u} refl

{-
X ---u---> Y 
|          |
|  id ⇒ id |
|          |
X ---u---> Y
-}
1⇒1 : ∀ {X Y} (u : X ⇒ Y) → Morphism⇒ C (record { arr = id {X} }) (record { arr = id {Y} })
1⇒1 u = mor⇒ {dom⇒ = u} {cod⇒ = u} (trans identityʳ (sym identityˡ))

open HomReasoning
open MR

-- d'oh!
-- ∀ u : Φ u ≈ Φ (id (cod u))
-- so that an MR system is constant when precomposed with each dom : C/b → C
module Naturalities {A B X Y} (ξ : MR2 A B) (u : X ⇒ Y) where
  open MR2

  Φid : (X : Obj) → X ⇒ [ A , X ]₀
  Φid X = Φη ξ (record { arr = id {A = X}})

  Φᵤ : Y ⇒ [ A , Y ]₀
  Φᵤ = Φη ξ (record { arr = u })
  
  -- naturality on 1⇒u:
  -- Φᵤ ∘ u ≈ [1,u] ∘ Φ₁
  nat-1⇒u : Φᵤ ∘ u ≈ [ id , u ]₁ ∘ Φid X
  nat-1⇒u = Φcommute ξ (1⇒u u)
  
  -- naturality on u⇒1:
  -- Φᵤ ≈ Φ₁ (identity of cod(u))
  nat-u⇒1 : Φid Y ≈ Φᵤ
  nat-u⇒1 = Equiv.sym identityʳ 
          ○ Φcommute ξ (u⇒1 u) 
          ○ (∘-resp-≈ˡ [-,-].identity) 
          ○ identityˡ

  -- naturality on 1⇒1:
  -- this is what implies that Φ is reduced to components of type id ≡> [A,-]
  -- because the square
  {-
    X ---- u ----> Y 
    |              |
Φ_{id X}           |Φ_{id Y}
    V              V
  [A,X] --[A,u]--> [A,Y] 
  -}
  nat-1⇒1 : Φid Y ∘ u ≈ [ id , u ]₁ ∘ Φid X
  nat-1⇒1 = Φcommute ξ (1⇒1 u)

open Naturalities

NICod⇒NIid : ∀ {A B} (ξ : MR2 A B) → NaturalTransformation idF ([_,-] A)
NICod⇒NIid ξ = let module ξ = MR2 ξ in ntHelper (record 
  { η = λ X → Naturalities.Φid ξ ξ.f X 
  ; commute = λ f → nat-1⇒1 ξ f 
  })

NIid⇒NICod : ∀ {A B} → (f : A ⇒ B) (φ : NaturalTransformation idF ([_,-] A)) → MR2 A B
NIid⇒NICod f φ = ⟪ f , ntHelper (record 
  { η = λ X → 
    let module X = Morphism X 
        module φ = NaturalTransformation φ
    in φ.η X.cod 
  ; commute = λ { {X} {Y} h → NaturalTransformation.commute φ (Morphism⇒.cod⇒ h) }
  }) ⟫


open import Categories.NaturalTransformation.NaturalIsomorphism as NI using (NaturalIsomorphism;niHelper; _ⓘˡ_; _ⓘʳ_)

fattoide : NaturalIsomorphism ([_,-] unit) idF
fattoide = niHelper (record 
  { η = λ X → adjoint.counit.η X ∘ unitorʳ.to
  ; η⁻¹ = λ X → adjoint.Ladjunct unitorʳ.from 
  ; commute = λ f → assoc ○ refl⟩∘⟨ unitorʳ-commute-to ○ pullˡ C (adjoint.counit.commute f) ○ assoc
  ; iso = λ X → 
    let λ₀ = unitorʳ.from 
        λ₀' = adjoint.Ladjunct λ₀
        ρ = unitorʳ.to
        module ε = NaturalTransformation adjoint.counit
    in record 
    { isoˡ = begin 
      λ₀' ∘ (ε.η X ∘ ρ)                                   ≈⟨ pullʳ C ((adjoint.unit.commute _)) ⟩
      [ id , λ₀ ]₁ ∘ adjoint.Ladjunct ((ε.η X ∘ ρ) ⊗₁ id) ≈˘⟨ pushˡ C ([ unit ,-] .Functor.homomorphism) ⟩
      adjoint.Ladjunct (λ₀ ∘ ((ε.η X ∘ ρ) ⊗₁ id))         ≈⟨ ([-,-].F-resp-≈ (Equiv.refl , unitorʳ-commute-from)) ⟩∘⟨refl ⟩
      adjoint.Ladjunct ((ε.η X ∘ ρ) ∘ λ₀)                 ≈⟨ ([-,-].F-resp-≈ (Equiv.refl , cancelʳ C unitorʳ.isoˡ)) ⟩∘⟨refl ⟩
      adjoint.Ladjunct (ε.η X)                            ≈⟨ adjoint.zag ⟩
      id                                                  ∎
    ; isoʳ = begin 
      (ε.η X ∘ ρ) ∘ λ₀'         ≈⟨ pullʳ C unitorʳ-commute-to ⟩
      ε.η X ∘ ((λ₀' ⊗₁ id) ∘ ρ) ≈⟨ sym-assoc ○ adjoint.RLadjunct≈id {f = λ₀} ⟩∘⟨refl ⟩
      λ₀ ∘ ρ                    ≈⟨ unitorʳ.isoʳ ⟩
      id                        ∎
    } 
  })

-- Type of the desired profunctor C.op × C → Sets
-- sending (A , B) ↦ MR2 A B.
MRS-Profunctor : Bifunctor (Category.op C) C (Setoids (o ⊔ ℓ ⊔ e) (o ⊔ ℓ ⊔ e))
MRS-Profunctor = record
  { F₀ = λ { (A , B) → MR2-Setoid A B }
  ; F₁ = λ { {(A , B)} {(A' , B')} (u , v) → record
    { _⟨$⟩_ = λ {⟪ f , Φ ⟫ → ⟪ v ∘ f ∘ u , (nHom u ∘ʳ Cod) ∘ᵥ Φ ⟫ }
    ; cong = λ { {⟪ f , Φ ⟫} {⟪ g , Φ' ⟫} (f≈g , Φ≈Φ') →
        (∘-resp-≈ Equiv.refl (∘-resp-≈ f≈g Equiv.refl))
      , (λ {x} → ∘-resp-≈ʳ (Φ≈Φ' {x}))
      }
    }}
  ; identity = λ { {(A , B)} {⟪ f , Φ ⟫} {⟪ g , Φ' ⟫} →
      let module Hom = Functor [-,-] in
      let module CodF = Functor Cod in
        ( λ (f≈g , Φ≈Φ') → Equiv.trans identityˡʳ f≈g
        , λ { {h} → Equiv.trans (elimˡ C Hom.identity) (Φ≈Φ' {h}) })
     }
  ; homomorphism = λ { {f = (u₁ , v₁)} {g = (u₂ , v₂)} {⟪ f , Φ ⟫} {⟪ g , Φ' ⟫} →
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
  ; F-resp-≈ = λ { {(A , B)} {(A' , B')} {f = (u , v)} {g = (u' , v')} (u≈u' , v≈v') {⟪ f , Φ ⟫} {⟪ g , Φ' ⟫} →
       let module Hom = Functor [-,-] in
         ( λ { (f≈g , Φ≈Φ') → ∘-resp-≈ v≈v' (∘-resp-≈ f≈g u≈u')
        , λ { {h} →
            let module Φ = NaturalTransformation Φ
                module Φ' = NaturalTransformation Φ'
            in ∘-resp-≈ (Hom.F-resp-≈ (u≈u' , Equiv.refl)) (Φ≈Φ' {h})
              } })
     }
  }