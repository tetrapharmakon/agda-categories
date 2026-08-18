{-# OPTIONS --without-K --warning=noUserWarning --warning=noUselessPrivate --warning=noUnsupportedIndexedMatch #-}

open import Categories.Category using (Category)
open import Categories.Category.Monoidal using (Monoidal)
open import Categories.Category.Monoidal.Closed using (Closed)
open import Level using (_⊔_)

module Categories.Rosen.Incoherent.Iterated {o ℓ e} {C : Category o ℓ e} {M : Monoidal C} (Cl : Closed M) where

-- Incoherent (M,R)-systems: a simple diagram A —f→ B —Φ→ [A,B]
-- without the natural transformation condition of full MR2.

open import Data.Product using (_,_; proj₁; proj₂; _×_)

open import Categories.Category.Construction.Arrow
open import Categories.Functor using (Functor)
open import Categories.Functor.Bifunctor using (appˡ; appʳ)
open import Categories.Functor.Bifunctor.Properties using ([_]-commute)
open import Categories.Morphism.Reasoning as MR

import Reason
open Reason C
open Closed Cl using ([-,-]; [_,_]₀; [_,_]₁)
open HomReasoning
open MR

-- module Arr = Categories.Category.Construction.Arrow C

open import Categories.Rosen.Incoherent.Core Cl  using (iMR2;iMR2₀;iMR2⇒;τ[iMR2];⟪_,_⟫)
open import Categories.Rosen.Incoherent.Functors Cl


{-
This implementation of the span composition 

 ↙ iMRS  ↘  ↙ iMRS  ↘
C         C          C

is simpler than the isoComma object.

here I want to define a category iMRSᴵᴵ having:

for objects iMRSᴵᴵ₀ a record containing as fields 
- an iMRS A B
- an iMRS B Y

for morphisms the "obvious" thing

-}

record iMRSᴵᴵ₀ : Set (o ⊔ ℓ) where
  field
    A B Y : Obj
    ξ₁ : iMR2 A B
    ξ₂ : iMR2 B Y
  hor : iMR2₀
  hor = record { A = A ; B = B ; ξ = ξ₁ }

  vert : iMR2₀
  vert = record { A = B ; B = Y ; ξ = ξ₂ }

record iMRSᴵᴵ⇒ (S T : iMRSᴵᴵ₀) : Set (o ⊔ ℓ ⊔ e) where
  module S = iMRSᴵᴵ₀ S
  module T = iMRSᴵᴵ₀ T
  field
    h : iMR2⇒ S.hor T.hor
    k : iMR2⇒ S.vert T.vert
  module h = iMR2⇒ h
  module k = iMR2⇒ k
  field
    hᵣ≈kₗ : h.r ≈ k.l

module τ[iMR2] = Category τ[iMR2]

iMRSᴵᴵ : Category (o ⊔ ℓ) (o ⊔ ℓ ⊔ e) e
iMRSᴵᴵ = record
  { Obj = iMRSᴵᴵ₀
  ; _⇒_ = λ s t → iMRSᴵᴵ⇒ s t
  ; _≈_ = λ p q → 
    let module p = iMRSᴵᴵ⇒ p 
        module q = iMRSᴵᴵ⇒ q 
    in (p.h τ[iMR2].≈ q.h) × (p.k τ[iMR2].≈ q.k)
  ; id = record 
    { h = τ[iMR2].id 
    ; k = τ[iMR2].id 
    ; hᵣ≈kₗ = Equiv.refl 
    }
  ; _∘_ = λ p q → 
    let module p = iMRSᴵᴵ⇒ p 
        module q = iMRSᴵᴵ⇒ q 
    in record 
      { h = p.h τ[iMR2].∘ q.h 
      ; k = p.k τ[iMR2].∘ q.k 
      ; hᵣ≈kₗ = ∘-resp-≈ p.hᵣ≈kₗ q.hᵣ≈kₗ 
      }
  ; assoc = (assoc , assoc) , (assoc , assoc)
  ; sym-assoc = (sym-assoc , sym-assoc) , (sym-assoc , sym-assoc)
  ; identityˡ = (identityˡ , identityˡ) , (identityˡ , identityˡ)
  ; identityʳ = (identityʳ , identityʳ) , identityʳ , identityʳ
  ; identity² = (identity² , identity²) , identity² , identity²
  -- junk automated proofs to refactor
  ; equiv = record 
    { refl = (refl , refl) , (refl , refl) 
    ; sym = λ x → (sym (x .proj₁ .proj₁) , sym (x .proj₁ .proj₂)) , sym (x .proj₂ .proj₁) , sym (x .proj₂ .proj₂)
    ; trans = λ x≈y y≈z → ((trans (x≈y .proj₁ .proj₁) (y≈z .proj₁ .proj₁)) , trans (x≈y .proj₁ .proj₂) (y≈z .proj₁ .proj₂)) , trans (x≈y .proj₂ .proj₁) (y≈z .proj₂ .proj₁) , trans (x≈y .proj₂ .proj₂) (y≈z .proj₂ .proj₂)
    }
  ; ∘-resp-≈ = λ f≈g f'≈g' → ((∘-resp-≈ (f≈g .proj₁ .proj₁) (f'≈g' .proj₁ .proj₁)) , ∘-resp-≈ (f≈g .proj₁ .proj₂) (f'≈g' .proj₁ .proj₂)) , (∘-resp-≈ (f≈g .proj₂ .proj₁) (f'≈g' .proj₂ .proj₁)) , ∘-resp-≈ (f≈g .proj₂ .proj₂) (f'≈g' .proj₂ .proj₂)
  }

deg₀² : Functor iMRSᴵᴵ τ[iMR2]
deg₀² = record
  { F₀ = λ x → 
    let module x = iMRSᴵᴵ₀ x 
    in record { A = x.A ; B = x.B ; ξ = x.ξ₁ }
  ; F₁ = λ S → let module S = iMRSᴵᴵ⇒ S in record 
    { l = S.h.l 
    ; r = S.h.r 
    ; eqf = S.h.eqf 
    ; eqΦ = S.h.eqΦ
    }
  ; identity = λ {A} → refl , refl -- refl , refl , refl , refl
  ; homomorphism = λ {X} {Y} {Z} {f} {g} → refl , refl -- refl , refl , refl , refl
  ; F-resp-≈ = λ {A} {B} {f} {g} z → z .proj₁ -- λ z → z .proj₁ .proj₁ , z .proj₂ .proj₁
  }

deg₂² : Functor iMRSᴵᴵ τ[iMR2]
deg₂² = record
  { F₀ = λ x → 
    let module x = iMRSᴵᴵ₀ x 
    in record { A = x.B ; B = x.Y ; ξ = x.ξ₂ }
  ; F₁ = λ S → let module S = iMRSᴵᴵ⇒ S in record 
    { l = S.k.l 
    ; r = S.k.r 
    ; eqf = S.k.eqf 
    ; eqΦ = S.k.eqΦ
    }
  ; identity = λ {A} → refl , refl -- refl , refl , refl , refl
  ; homomorphism = λ {X} {Y} {Z} {f} {g} → refl , refl -- refl , refl , refl , refl
  ; F-resp-≈ = λ {A} {B} {f} {g} z → z .proj₂ -- λ z → z .proj₁ .proj₁ , z .proj₂ .proj₁
  }

comp : Functor iMRSᴵᴵ τ[iMR2]
comp = record
  { F₀ = λ x → 
    let module x = iMRSᴵᴵ₀ x 
        f = iMR2.f x.ξ₁
        g = iMR2.f x.ξ₂
        Φ = iMR2.Φ x.ξ₁
        Ψ = iMR2.Φ x.ξ₂
    in record { A = x.A ; B = x.Y ; ξ = ⟪ g ∘ f , [ f , id ]₁ ∘ Ψ ⟫ }
  ; F₁ = λ S → let module S = iMRSᴵᴵ⇒ S in record 
    { l = S.h.l 
    ; r = S.k.r 
    ; eqf = 
        let r' = S.k.r
            l' = S.k.l
            r = S.h.r
            l = S.h.l
            g = S.h.ξX.f
            f = S.k.ξX.f
            f' = S.k.ξY.f
            g' = S.h.ξY.f
        in begin
        r' ∘ (f ∘ g)  ≈⟨ sym-assoc ○ S.k.eqf ⟩∘⟨refl ⟩
        (f' ∘ l') ∘ g ≈⟨ assoc ○ refl⟩∘⟨ (Equiv.sym S.hᵣ≈kₗ ⟩∘⟨refl) ⟩
        f' ∘ (r ∘ g)  ≈⟨ refl⟩∘⟨ S.h.eqf ○ sym-assoc ⟩
        (f' ∘ g') ∘ l ∎
    ; eqΦ = let module HomR {A} = Functor (appʳ [-,-] A)
                module HomL {A} = Functor (appˡ [-,-] A)
                r' = S.k.r
                l' = S.k.l
                r = S.h.r
                l = S.h.l
                g = S.h.ξX.f
                f = S.k.ξX.f
                f' = S.k.ξY.f
                g' = S.h.ξY.f
                Ψ = S.k.ξY.Φ
                Φ = S.k.ξX.Φ
            in begin
        [ l , id ]₁ ∘ ([ g' , id ]₁ ∘ Ψ) ∘ r' ≈⟨ refl⟩∘⟨ assoc ○ sym-assoc ○ (Equiv.sym HomR.homomorphism) ⟩∘⟨refl ⟩
        [ g' ∘ l , id ]₁ ∘ Ψ ∘ r'             ≈⟨ HomR.F-resp-≈ (Equiv.sym S.h.eqf) ⟩∘⟨refl ⟩
        [ r ∘ g , id ]₁ ∘ Ψ ∘ r'              ≈⟨ HomR.homomorphism ⟩∘⟨refl ○ assoc ⟩
        [ g , id ]₁ ∘ [ r , id ]₁ ∘ Ψ ∘ r'    ≈⟨ refl⟩∘⟨ (HomR.F-resp-≈ S.hᵣ≈kₗ ⟩∘⟨refl) ⟩
        [ g , id ]₁ ∘ [ l' , id ]₁ ∘ Ψ ∘ r'   ≈⟨ refl⟩∘⟨ S.k.eqΦ ○ sym-assoc ⟩
        ([ g , id ]₁ ∘ [ id , r' ]₁) ∘ Φ      ≈⟨ (Equiv.sym [ [-,-] ]-commute) ⟩∘⟨refl ○ assoc ⟩
        [ id , r' ]₁ ∘ [ g , id ]₁ ∘ Φ        ∎
    }
  ; identity = refl , refl
  ; homomorphism = refl , refl
  ; F-resp-≈ = λ x → x .proj₁ .proj₁ , x .proj₂ .proj₂
  }