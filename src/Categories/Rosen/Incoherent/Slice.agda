{-# OPTIONS --without-K --warning=noUserWarning --warning=noUselessPrivate --warning=noUnsupportedIndexedMatch #-}

open import Categories.Category using (Category)
open import Level using (_⊔_)
open import Categories.Category.BinaryProducts using (BinaryProducts)
open import Categories.Category.Monoidal using (Monoidal)
open import Categories.Category.Monoidal.Closed using (Closed)
open import Categories.Category.Monoidal.Symmetric using (Symmetric)

module Categories.Rosen.Incoherent.Slice
  {o ℓ e} {C : Category o ℓ e}
  (M : Monoidal C)
  (Cl : Closed M)
  (S : Symmetric M)
  (BC : BinaryProducts C)
  where

------------------------------------------------------------------------
-- Incoherent (M,R)-systems as algebras
--
-- Fix an object B... (todo)
------------------------------------------------------------------------

open Category C

open import Categories.Category.Equivalence using (StrongEquivalence)
open import Categories.Functor using (Functor; _∘F_)
open import Categories.Functor.Bifunctor using (appˡ; appʳ)
open import Categories.Functor.Bifunctor.Properties using ([_]-decompose₁;[_]-commute)
import Categories.Morphism.Reasoning as MR
open import Categories.NaturalTransformation.NaturalIsomorphism using (niHelper)
open import Categories.Rosen.Incoherent.Core Cl
open import Categories.Rosen.Incoherent.Displayed Cl using (iMR2ᴸ; iMR2ᴸ₀; iMR2ᴸ⇒)
open import Data.Product using (_,_)

import Categories.Category.Slice as Sl


open HomReasoning
open MR C
open Monoidal M using (_⊗-; -⊗_; unit; _⊗₀_; _⊗₁_)
open BinaryProducts BC

open Symmetric S hiding (_⊗-; -⊗_; unit; _⊗₀_; _⊗₁_) renaming (braided-iso to β)
open Closed Cl using (adjoint; mate; [-,-]; [_,_]₀; [_,_]₁; [_,-])

slice : (B : Obj) → Category (o ⊔ ℓ) (ℓ ⊔ e) e
slice B = Sl.Slice C (B × [ B , B ]₀)


module To {B : Obj} {X Y : iMR2ᴸ₀ B} (f : iMR2ᴸ⇒ X Y) where
  module X = iMR2ᴸ₀ X
  module Y = iMR2ᴸ₀ Y
  module f = iMR2ᴸ⇒ f
  ε₀ = adjoint.counit.η
  η₀ = adjoint.unit.η

  cowedge : ∀ {A A′} {u : A ⇒ A′} → ε₀ B ∘ id ⊗₁ u ≈ ε₀ B ∘ [ u , id ]₁ ⊗₁ id
  cowedge = Equiv.sym (mate.commute₂ _)

  q-comm :
    adjoint.Ladjunct (adjoint.Radjunct f.ξY.Φ ∘ β.from) ∘ f.u
      ≈ adjoint.Ladjunct (adjoint.Radjunct f.ξX.Φ ∘ β.from)
  q-comm =
    begin ([ id , (ε₀ _ ∘ f.ξY.Φ ⊗₁ id) ∘ β.from ]₁ ∘ η₀ _) ∘ f.u
            ≈⟨ pullʳ (adjoint.unit.commute f.u) ⟩
          [ id , (ε₀ _ ∘ f.ξY.Φ ⊗₁ id) ∘ β.from ]₁ ∘ [ id , f.u ⊗₁ id ]₁ ∘ η₀ _
            ≈⟨ pullˡ (Equiv.sym (Functor.homomorphism [ _ ,-])) ⟩
          [ id , ((ε₀ _ ∘ f.ξY.Φ ⊗₁ id) ∘ β.from) ∘ f.u ⊗₁ id ]₁ ∘ η₀ _
            ≈⟨ Functor.F-resp-≈ [ _ ,-] (pullʳ (braiding.⇒.commute (f.u , id))) ⟩∘⟨refl ⟩
          [ id , (ε₀ _ ∘ f.ξY.Φ ⊗₁ id) ∘ id ⊗₁ f.u ∘ β.from ]₁ ∘ η₀ _
             ≈⟨ Functor.F-resp-≈ [ _ ,-] assoc ⟩∘⟨refl ⟩
          [ id , ε₀ _ ∘ (f.ξY.Φ ⊗₁ id ∘ id ⊗₁ f.u ∘ β.from) ]₁ ∘ η₀ _
            ≈⟨ Functor.F-resp-≈ [ _ ,-] (refl⟩∘⟨ pullˡ (Equiv.sym [ ⊗ ]-commute)) ⟩∘⟨refl ⟩
          [ id , ε₀ _ ∘ (id ⊗₁ f.u ∘ f.ξY.Φ ⊗₁ id) ∘ β.from ]₁ ∘ η₀ _
            ≈⟨ Functor.F-resp-≈ [ _ ,-] (refl⟩∘⟨ assoc ○ pullˡ cowedge) ⟩∘⟨refl ⟩
          [ id , (ε₀ _ ∘ [ f.u , id ]₁ ⊗₁ id) ∘ f.ξY.Φ ⊗₁ id ∘ β.from ]₁ ∘ η₀ _
            ≈⟨ Functor.F-resp-≈ [ _ ,-] (assoc ○ (refl⟩∘⟨ sym-assoc) ○ sym-assoc) ⟩∘⟨refl ⟩
          [ id , (ε₀ _ ∘ [ f.u , id ]₁ ⊗₁ id ∘ f.ξY.Φ ⊗₁ id) ∘ β.from ]₁ ∘ η₀ f.X.A
            ≈˘⟨ Functor.F-resp-≈ [ _ ,-] ((refl⟩∘⟨ Functor.homomorphism (-⊗ _)) ⟩∘⟨refl) ⟩∘⟨refl ⟩
          [ id , (ε₀ _ ∘ ([ f.u , id ]₁ ∘ f.ξY.Φ) ⊗₁ id) ∘ β.from ]₁ ∘ η₀ f.X.A
            ≈˘⟨ Functor.F-resp-≈ [ _ ,-] ((refl⟩∘⟨ Functor.F-resp-≈ (-⊗ _) f.eqΦ) ⟩∘⟨refl) ⟩∘⟨refl ⟩
          [ id , (ε₀ _ ∘ f.ξX.Φ ⊗₁ id) ∘ β.from ]₁ ∘ η₀ f.X.A ∎

to : {B : Obj} → Functor (iMR2ᴸ B) (slice B)
to {B} = record
  { F₀ = λ x →
    let module x = iMR2ᴸ₀ x
        ΦX# = adjoint.Radjunct (iMR2.Φ x.ξ)
    in Sl.sliceobj {Y = x.A}
    ⟨ iMR2.f x.ξ
    , adjoint.Ladjunct (ΦX# ∘ β.from) ⟩
  ; F₁ = λ { {X} {Y} f →
     let module X = iMR2ᴸ₀ X
         module Y = iMR2ᴸ₀ Y
         module f = iMR2ᴸ⇒ f
     in Sl.slicearr {h = f.u}
       (begin
         ⟨ f.ξY.f , adjoint.Ladjunct (adjoint.Radjunct f.ξY.Φ ∘ β.from) ⟩ ∘ f.u
           ≈⟨ ⟨⟩∘ ⟩
         ⟨ f.ξY.f ∘ f.u
         , adjoint.Ladjunct (adjoint.Radjunct f.ξY.Φ ∘ β.from) ∘ f.u ⟩
           ≈⟨ ⟨⟩-cong₂ (Equiv.sym f.eqf) (To.q-comm f) ⟩
         ⟨ f.ξX.f
         , adjoint.Ladjunct (adjoint.Radjunct f.ξX.Φ ∘ β.from) ⟩ ∎) }
  ; identity = Equiv.refl
  ; homomorphism = Equiv.refl
  ; F-resp-≈ = λ z → z
  }

-- Converse functor slice → iMR2ᴸ B.
from : {B : Obj} → Functor (slice B) (iMR2ᴸ B)
from {B} = record
  { F₀ = λ x →
      let module x = Sl.SliceObj x
          π₂x# = adjoint.Radjunct (π₂ ∘ x.arr)
      in record
        { A = x.Y
        ; ξ = ⟪ π₁ ∘ x.arr , adjoint.Ladjunct (π₂x# ∘ β.from) ⟫
        }
  ; F₁ = λ { {X} {Y} f →
      let module X = Sl.SliceObj X
          module Y = Sl.SliceObj Y
          module f = Sl.Slice⇒ f
          ε₀ = adjoint.counit.η
          η₀ = adjoint.unit.η
          g1 = π₂ ∘ X.arr
          g2 = π₂ ∘ Y.arr
          eqg : g1 ≈ g2 ∘ f.h
          eqg = (refl⟩∘⟨ Equiv.sym f.△) ○ sym-assoc
          k = ε₀ _ ∘ g2 ⊗₁ id
          -- naturality of Ladjunct across a change of exponent along f.h,
          -- via the mate square between adjoint{X.Y} and adjoint{Y.Y}
          wedge : [ id , id ⊗₁ f.h ]₁ ∘ η₀ _ ≈ [ f.h , id ]₁ ∘ η₀ _
          wedge = mate.commute₁ _
          wedge2 : adjoint.Ladjunct ((k ∘ β.from) ∘ id ⊗₁ f.h) ≈ [ f.h , id ]₁ ∘ adjoint.Ladjunct (k ∘ β.from)
          wedge2 = begin
            [ id , (k ∘ β.from) ∘ id ⊗₁ f.h ]₁ ∘ η₀ _
              ≈⟨ Functor.homomorphism [ _ ,-] ⟩∘⟨refl ⟩
            ([ id , k ∘ β.from ]₁ ∘ [ id , id ⊗₁ f.h ]₁) ∘ η₀ _
              ≈⟨ assoc ⟩
            [ id , k ∘ β.from ]₁ ∘ [ id , id ⊗₁ f.h ]₁ ∘ η₀ _
              ≈⟨ refl⟩∘⟨ wedge ⟩
            [ id , k ∘ β.from ]₁ ∘ [ f.h , id ]₁ ∘ η₀ _
              ≈⟨ sym-assoc ⟩
            ([ id , k ∘ β.from ]₁ ∘ [ f.h , id ]₁) ∘ η₀ _
              ≈⟨ [ [-,-] ]-commute ⟩∘⟨refl ⟩
            ([ f.h , id ]₁ ∘ [ id , k ∘ β.from ]₁) ∘ η₀ _
              ≈⟨ assoc ⟩
            [ f.h , id ]₁ ∘ [ id , k ∘ β.from ]₁ ∘ η₀ _
              ∎
      in record
        { u = f.h
        ; eqf = pushʳ (Equiv.sym f.△)
        ; eqΦ =
          begin
            adjoint.Ladjunct (adjoint.Radjunct g1 ∘ β.from)
              ≈⟨ adjoint.Ladjunct-resp-≈ ((refl⟩∘⟨ Functor.F-resp-≈ (-⊗ _) eqg) ⟩∘⟨refl) ⟩
            adjoint.Ladjunct ((ε₀ _ ∘ (g2 ∘ f.h) ⊗₁ id) ∘ β.from)
              ≈⟨ adjoint.Ladjunct-resp-≈ ((refl⟩∘⟨ Functor.homomorphism (-⊗ _)) ⟩∘⟨refl) ⟩
            adjoint.Ladjunct ((ε₀ _ ∘ g2 ⊗₁ id ∘ f.h ⊗₁ id) ∘ β.from)
              ≈⟨ adjoint.Ladjunct-resp-≈ (sym-assoc ⟩∘⟨refl) ⟩
            adjoint.Ladjunct (((ε₀ _ ∘ g2 ⊗₁ id) ∘ f.h ⊗₁ id) ∘ β.from)
              ≈⟨ adjoint.Ladjunct-resp-≈ (pullʳ (braiding.⇒.sym-commute (id , f.h))) ⟩
            adjoint.Ladjunct (k ∘ β.from ∘ id ⊗₁ f.h)
              ≈⟨ adjoint.Ladjunct-resp-≈ sym-assoc ⟩
            adjoint.Ladjunct ((k ∘ β.from) ∘ id ⊗₁ f.h)
              ≈⟨ wedge2 ⟩
            [ f.h , id ]₁ ∘ adjoint.Ladjunct (k ∘ β.from)
          ∎
        } }
  ; identity = Equiv.refl
  ; homomorphism = Equiv.refl
  ; F-resp-≈ = λ z → z
  }

------------------------------------------------------------------------
-- Equivalence
------------------------------------------------------------------------

AlgA≣MRS-B : {B : Obj} → StrongEquivalence (iMR2ᴸ B) (slice B)
AlgA≣MRS-B {B} = record
  { F = to
  ; G = from
  ; weak-inverse = record
     { F∘G≈id = niHelper (record
       { η = λ X →
         let module X = Sl.SliceObj X
             f = π₁ ∘ X.arr
             g = π₂ ∘ X.arr
             g# = adjoint.Radjunct g
          in Sl.slicearr {h = id} (identityʳ ○
          (begin Sl.SliceObj.arr X
                  ≈˘⟨ identityˡ ⟩
                 id ∘ X.arr
                  ≈˘⟨ ∘-resp-≈ˡ η ⟩
                 ⟨ π₁ , π₂ ⟩ ∘ X.arr
                  ≈⟨ ⟨⟩∘ ⟩
                 ⟨ π₁ ∘ X.arr , π₂ ∘ X.arr ⟩
                  ≈˘⟨ ⟨⟩-congˡ (adjoint.LRadjunct≈id {f = g}) ⟩
                ⟨ π₁ ∘ X.arr , adjoint.Ladjunct g# ⟩
                  ≈˘⟨ ⟨⟩-congˡ (adjoint.Ladjunct-resp-≈ (elimʳ commutative)) ⟩
                ⟨ π₁ ∘ X.arr , adjoint.Ladjunct (g# ∘ β.from ∘ β.from) ⟩
                  ≈˘⟨ ⟨⟩-congˡ (adjoint.Ladjunct-resp-≈ assoc) ⟩
                ⟨ π₁ ∘ X.arr , adjoint.Ladjunct ((g# ∘ β.from) ∘ β.from) ⟩
                  ≈˘⟨ ⟨⟩-congˡ (adjoint.Ladjunct-resp-≈ (adjoint.RLadjunct≈id ⟩∘⟨refl)) ⟩
                ⟨ π₁ ∘ X.arr , adjoint.Ladjunct (adjoint.Radjunct (adjoint.Ladjunct (g# ∘ β.from)) ∘ β.from) ⟩ ∎))
       ; η⁻¹ = λ X →
         let module X = Sl.SliceObj X
             f = π₁ ∘ X.arr
             g = π₂ ∘ X.arr
             g# = adjoint.Radjunct g in Sl.slicearr {h = id} (identityʳ ○ Equiv.sym
               (begin Sl.SliceObj.arr X
                  ≈˘⟨ identityˡ ⟩
                 id ∘ X.arr
                  ≈˘⟨ ∘-resp-≈ˡ η ⟩
                 ⟨ π₁ , π₂ ⟩ ∘ X.arr
                  ≈⟨ ⟨⟩∘ ⟩
                 ⟨ π₁ ∘ X.arr , π₂ ∘ X.arr ⟩
                  ≈˘⟨ ⟨⟩-congˡ (adjoint.LRadjunct≈id {f = g}) ⟩
                ⟨ π₁ ∘ X.arr , adjoint.Ladjunct g# ⟩
                  ≈˘⟨ ⟨⟩-congˡ (adjoint.Ladjunct-resp-≈ (elimʳ commutative)) ⟩
                ⟨ π₁ ∘ X.arr , adjoint.Ladjunct (g# ∘ β.from ∘ β.from) ⟩
                  ≈˘⟨ ⟨⟩-congˡ (adjoint.Ladjunct-resp-≈ assoc) ⟩
                ⟨ π₁ ∘ X.arr , adjoint.Ladjunct ((g# ∘ β.from) ∘ β.from) ⟩
                  ≈˘⟨ ⟨⟩-congˡ (adjoint.Ladjunct-resp-≈ (adjoint.RLadjunct≈id ⟩∘⟨refl)) ⟩
                ⟨ π₁ ∘ X.arr , adjoint.Ladjunct (adjoint.Radjunct (adjoint.Ladjunct (g# ∘ β.from)) ∘ β.from) ⟩ ∎))
       ; commute = λ f → identityˡ ○ Equiv.sym identityʳ
       ; iso = λ X → record { isoˡ = identityˡ ; isoʳ = identityˡ }
       })
     ; G∘F≈id = niHelper (record
       { η = λ X →
         let module X = iMR2ᴸ₀ X
             module Xξ = iMR2 X.ξ
             Φ# = adjoint.Radjunct Xξ.Φ
         in record
         { u = id
         ; eqf = Equiv.trans project₁ (Equiv.sym identityʳ)
         ; eqΦ =
           (begin
             adjoint.Ladjunct (adjoint.Radjunct (π₂ ∘ ⟨ Xξ.f , adjoint.Ladjunct (Φ# ∘ β.from) ⟩) ∘ β.from)
               ≈⟨ adjoint.Ladjunct-resp-≈ (adjoint.Radjunct-resp-≈ project₂ ⟩∘⟨refl) ⟩
             adjoint.Ladjunct (adjoint.Radjunct (adjoint.Ladjunct (Φ# ∘ β.from)) ∘ β.from)
               ≈⟨ adjoint.Ladjunct-resp-≈ (adjoint.RLadjunct≈id ⟩∘⟨refl) ⟩
             adjoint.Ladjunct ((Φ# ∘ β.from) ∘ β.from)
               ≈⟨ adjoint.Ladjunct-resp-≈ assoc ⟩
             adjoint.Ladjunct (Φ# ∘ (β.from ∘ β.from))
               ≈⟨ adjoint.Ladjunct-resp-≈ (elimʳ commutative) ⟩
             adjoint.Ladjunct Φ#
               ≈⟨ adjoint.LRadjunct≈id ⟩
             Xξ.Φ
               ≈˘⟨ identityˡ ⟩
             id ∘ Xξ.Φ
               ≈˘⟨ Functor.identity [-,-] ⟩∘⟨refl ⟩
             [ id , id ]₁ ∘ Xξ.Φ ∎)
         }
       ; η⁻¹ = λ X →
         let module X = iMR2ᴸ₀ X
             module Xξ = iMR2 X.ξ
             Φ# = adjoint.Radjunct Xξ.Φ
         in record
         { u = id
         ; eqf = Equiv.sym identityʳ ○ (Equiv.sym project₁ ⟩∘⟨refl)
         ; eqΦ = Equiv.sym
           (elimˡ (Functor.identity [-,-]) ○ (begin
             adjoint.Ladjunct (adjoint.Radjunct (π₂ ∘ ⟨ Xξ.f , adjoint.Ladjunct (Φ# ∘ β.from) ⟩) ∘ β.from)
               ≈⟨ adjoint.Ladjunct-resp-≈ (adjoint.Radjunct-resp-≈ project₂ ⟩∘⟨refl) ⟩
             adjoint.Ladjunct (adjoint.Radjunct (adjoint.Ladjunct (Φ# ∘ β.from)) ∘ β.from)
               ≈⟨ adjoint.Ladjunct-resp-≈ (adjoint.RLadjunct≈id ⟩∘⟨refl) ⟩
             adjoint.Ladjunct ((Φ# ∘ β.from) ∘ β.from)
               ≈⟨ adjoint.Ladjunct-resp-≈ assoc ⟩
             adjoint.Ladjunct (Φ# ∘ (β.from ∘ β.from))
               ≈⟨ adjoint.Ladjunct-resp-≈ (elimʳ commutative) ⟩
             adjoint.Ladjunct Φ#
               ≈⟨ adjoint.LRadjunct≈id ⟩
             Xξ.Φ ∎))
         }
       ; commute = λ X → identityˡ ○ Equiv.sym identityʳ
       ; iso = λ X → record { isoˡ = identityˡ ; isoʳ = identityˡ } })
    }
  }
