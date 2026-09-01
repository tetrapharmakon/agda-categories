{-# OPTIONS --safe --without-K --warning=noUserWarning --warning=noUselessPrivate --warning=noUnsupportedIndexedMatch #-}

open import Categories.Category using (Category)
open import Categories.Category.Monoidal using (Monoidal)
open import Categories.Category.Monoidal.Closed using (Closed)
open import Level using (_⊔_)

module Categories.Rosen.Incoherent.Functors {o ℓ e} {C : Category o ℓ e} {M : Monoidal C} (Cl : Closed M) where

------------------------------------------------------------------------
-- Functors: projections out of the total category τ[iMR2].
--
-- [_]A, [_]B, [_]f, [_]Φ recover respectively the domain, the
-- codomain, the process arrow and the repair map of a system.  The
-- file ends with the Arbib functor from twisted MR-systems to the
-- internal Mealy automata of Mealy.agda (see the two lemmas below).
------------------------------------------------------------------------

open import Data.Product using (_,_; proj₁; proj₂; _×_)

open import Categories.Category.Construction.Arrow
open import Categories.Functor using (Functor;_∘F_)
open import Categories.Functor.Bifunctor using (appˡ; appʳ)
open import Categories.Functor.Bifunctor.Properties using ([_]-commute;[_]-decompose₁;[_]-decompose₂;[_]-merge)
open import Categories.Morphism.Reasoning as MR

import Reason
open Reason C
open Closed Cl using (adjoint; mate;[-,-]; [_,_]₀; [_,_]₁;⊗;_⊗₀_;_⊗₁_;_⊗-;-⊗_)
open HomReasoning
open MR

open import Categories.Rosen.Incoherent.Core Cl
open import Categories.Rosen.Incoherent.Elements Cl

-- [_]A : τ[iMR2] → C — the projection onto the domain object A.
[_]A : Functor τ[iMR2] C
[_]A = record
  { F₀ = λ x → let module x = iMR2₀ x in x.A
  ; F₁ = λ f → let module f = iMR2⇒ f in f.l
  ; identity = λ {A} → refl
  ; homomorphism = λ {X} {Y} {Z} {f} {g} → refl
  ; F-resp-≈ = λ {A} {B} {f} {g} z → z .proj₁
  }

-- [_]B : τ[iMR2] → C — the projection onto the codomain object B.
[_]B : Functor τ[iMR2] C
[_]B = record
  { F₀ = λ x → let module x = iMR2₀ x in x.B
  ; F₁ = λ f → let module f = iMR2⇒ f in f.r
  ; identity = λ {B} → refl
  ; homomorphism = λ {X} {Y} {Z} {f} {g} → refl
  ; F-resp-≈ = λ {A} {B} {f} {g} z → z .proj₂
  }

-- [_]f : τ[iMR2] → Arrow(C) — the process arrow f : A ⇒ B as an object
-- of the arrow category; morphisms are carried via the eqf square.
[_]f : Functor τ[iMR2] Arr.Arrow
[_]f = record
  { F₀ = λ x → let module x = iMR2₀ x in record { dom = x.A ; cod = x.B ; arr = iMR2.f x.ξ }
  ; F₁ = λ f → let module f = iMR2⇒ f in mor⇒ f.eqf
  ; identity = refl , refl
  ; homomorphism = refl , refl
  ; F-resp-≈ = λ x → x
  }

open import Categories.Rosen.Incoherent.Repairs Cl

-- [_]Φ : τ[iMR2] → irepairs — the repair map Φ for each system, as an
-- object of the repair category (forgetting the process data).
[_]Φ : Functor τ[iMR2] irepairs
[_]Φ = record
  { F₀ = λ x → let module x = iMR2₀ x in record
    { A = x.A
    ; B = x.B
    ; Φ = iMR2.Φ x.ξ
    }
  ; F₁ = λ f → let module f = iMR2⇒ f in record
    { u = f.l
    ; v = f.r
    ; eq = f.eqΦ
    }
  ; identity = refl
  ; homomorphism = refl
  ; F-resp-≈ = λ z → z .proj₁
  }


open import Categories.Rosen.Incoherent.Mealy Cl

-- A functor from the category of twisted MR systems to the category of twisted Mealy automata
-- cf. Categories.Rosen.Incoherent.Mealy for the definition
-- the functor was defined by Arbib in \cite{}
--
-- On objects the automaton has state E = [A,B]₀, transition d given by
-- the Ladjunct of (Φ* ∘ (ε ⊗₁ id)) and output s given by the counit.
-- The squares forced by a twisted morphism are exactly lemma-delta
-- (transition component) and lemma-epsilon (output component).

module _ {X Y : iMR2₀} (f : twiMR2⇒ X Y) where
  module X = iMR2₀ X
  ΦX = iMR2.Φ X.ξ
  ΦX* = adjoint.Radjunct ΦX
  module Y = iMR2₀ Y
  ΦY = iMR2.Φ Y.ξ
  ΦY* = adjoint.Radjunct ΦY
  module F = twiMR2⇒ f
  ε = adjoint.counit.η
  module -⊗A = Functor (appʳ ⊗ F.Y.A)
  module [A-] = Functor (appˡ [-,-] F.Y.A)

  -- lemma-epsilon: the output square — the counit ε of the closed
  -- adjunction conjugates the twisted (l, r) action on the output map.
  lemma-epsilon :
    F.r ∘ ε X.B ∘ id ⊗₁ F.l ≈ ε Y.B ∘ [ F.l , F.r ]₁ ⊗₁ id
  lemma-epsilon =
    begin F.r ∘ ε X.B ∘ id ⊗₁ F.l                             ≈⟨ pullˡ C (adjoint.counit.sym-commute F.r) ∙ assoc ⟩
          ε Y.B ∘ [ id , F.r ]₁ ⊗₁ id ∘ id ⊗₁ F.l             ≈⟨ (refl⟩∘⟨ Equiv.sym [ ⊗ ]-commute) ⟩
          ε Y.B ∘ id ⊗₁ F.l ∘ [ id , F.r ]₁ ⊗₁ id             ≈⟨ pullˡ C (Equiv.sym (mate.commute₂ F.l {F.Y.B})) ⟩
          (ε Y.B ∘ [ F.l , id ]₁ ⊗₁ id) ∘ [ id , F.r ]₁ ⊗₁ id ≈⟨ assoc ⟩
          ε Y.B ∘ [ F.l , id ]₁ ⊗₁ id ∘ [ id , F.r ]₁ ⊗₁ id   ≈˘⟨ refl⟩∘⟨ -⊗A.homomorphism ⟩
          ε Y.B ∘ ([ F.l , id ]₁ ∘ [ id , F.r ]₁) ⊗₁ id       ≈˘⟨ refl⟩∘⟨ -⊗A.F-resp-≈ [ [-,-] ]-decompose₁ ⟩
          ε Y.B ∘ [ F.l , F.r ]₁ ⊗₁ id                                                     ∎

  -- lemma-delta: the transition square — the Ladjunct of Φ* ∘ (ε ⊗₁ id)
  -- (i.e. the transition of the Mealy automaton) transports along a
  -- twisted MR-morphism.
  lemma-delta :
    [ F.l , F.r ]₁ ∘ adjoint.Ladjunct (ΦX* ∘ (ε X.B ⊗₁ id)) ∘ id ⊗₁ F.l
      ≈
    adjoint.Ladjunct (ΦY* ∘ (ε Y.B ⊗₁ id)) ∘ [ F.l , F.r ]₁ ⊗₁ id
  lemma-delta =
    begin [ F.l , F.r ]₁ ∘ adjoint.Ladjunct (ΦX* ∘ ε F.X.B ⊗₁ id) ∘ id ⊗₁ F.l                 ≈⟨ refl⟩∘⟨ (adjoint.Ladjunct-comm′ ∙ ((adjoint.LRadjunct≈id ⟩∘⟨refl)) ⟩∘⟨refl) ⟩
          [ F.l , F.r ]₁ ∘ (ΦX ∘ ε F.X.B) ∘ id ⊗₁ F.l                                         ≈⟨ refl⟩∘⟨ pullʳ C (Equiv.sym (mate.commute₂ F.l)) ⟩
          [ F.l , F.r ]₁ ∘ ΦX ∘ ε F.X.B ∘ ([ F.l , id ]₁ ⊗₁ id)                               ≈⟨ refl⟩∘⟨ pullˡ C (adjoint.counit.sym-commute F.ξX.Φ) ⟩
          [ F.l , F.r ]₁ ∘ (ε _ ∘ [ id , ΦX ]₁ ⊗₁ id) ∘ ([ F.l , id ]₁ ⊗₁ id)                 ≈⟨ sym-assoc ∙ (pullˡ C (adjoint.counit.sym-commute _) ⟩∘⟨refl) ⟩
          ((ε _ ∘ [ id , [ F.l , F.r ]₁ ]₁ ⊗₁ id) ∘ [ id , ΦX ]₁ ⊗₁ id) ∘ [ F.l , id ]₁ ⊗₁ id ≈⟨ anti-assoc-4 ∙ (refl⟩∘⟨ Equiv.sym ((-⊗A.homomorphism ○ refl⟩∘⟨ -⊗A.homomorphism))) ⟩
          ε _ ∘ ([ id , [ F.l , F.r ]₁ ]₁ ∘ [ id , ΦX ]₁ ∘ [ F.l , id ]₁) ⊗₁ id               ≈⟨ refl⟩∘⟨ -⊗A.F-resp-≈ (pullˡ C (Equiv.sym ([A-].homomorphism))) ⟩
          ε _ ∘ ([ id , [ F.l , F.r ]₁ ∘ ΦX ]₁ ∘ [ F.l , id ]₁) ⊗₁ id                         ≈⟨ refl⟩∘⟨ -⊗A.F-resp-≈ ([A-].F-resp-≈ (sym F.eqΦ) ⟩∘⟨refl) ⟩
          ε _ ∘ ([ id , ΦY ∘ F.r ]₁ ∘ [ F.l , id ]₁) ⊗₁ id                                    ≈⟨ refl⟩∘⟨ -⊗A.homomorphism ⟩
          ε _ ∘ ([ id , ΦY ∘ F.r ]₁ ⊗₁ id ∘ [ F.l , id ]₁ ⊗₁ id)                              ≈⟨ pullˡ C (adjoint.counit.commute _) ⟩
          ((ΦY ∘ F.r) ∘ ε F.X.B) ∘ [ F.l , id ]₁ ⊗₁ id                                        ≈⟨ (pullʳ C (adjoint.counit.sym-commute F.r) ⟩∘⟨refl) ○ assoc-3 ⟩
          ΦY ∘ ε F.Y.B ∘ ([ id , F.r ]₁ ⊗₁ id) ∘ [ F.l , id ]₁ ⊗₁ id                          ≈˘⟨ skip-2 -⊗A.homomorphism ⟩
          ΦY ∘ ε F.Y.B ∘ ([ id , F.r ]₁ ∘ [ F.l , id ]₁) ⊗₁ id                                ≈˘⟨ skip-2 (-⊗A.F-resp-≈ [ [-,-] ]-decompose₂) ⟩
          F.ξY.Φ ∘ ε F.Y.B ∘ [ F.l , F.r ]₁ ⊗₁ id                                             ≈⟨ sym-assoc ⟩
          (ΦY ∘ ε F.Y.B) ∘ [ F.l , F.r ]₁ ⊗₁ id                                               ≈˘⟨ (adjoint.LRadjunct≈id ⟩∘⟨refl) ⟩∘⟨refl ⟩
          ((adjoint.Ladjunct ΦY*) ∘ ε F.Y.B) ∘ [ F.l , F.r ]₁ ⊗₁ id                           ≈˘⟨ adjoint.Ladjunct-comm′ ⟩∘⟨refl ⟩
          adjoint.Ladjunct (ΦY* ∘ ε F.Y.B ⊗₁ id) ∘ [ F.l , F.r ]₁ ⊗₁ id                       ∎

Arbib : Functor τ′[iMR2] twMealy
Arbib = record
  { F₀ = λ x →
    let module x = iMR2₀ x
        module ξX = iMR2 x.ξ
        Φ* = adjoint.Radjunct ξX.Φ
    in record
    { A = x.A
    ; B = x.B
    ; m = record
      { E = [ x.A , x.B ]₀
      ; d = adjoint.Ladjunct (Φ* ∘ (adjoint.counit.η x.B ⊗₁ id))
      ; s = adjoint.counit.η x.B
      }
    }
  ; F₁ = λ f →
    let module f = twiMR2⇒ f
        module AX = adjoint {f.X.A}
        module AY = adjoint {f.Y.A}
        εXB = AX.counit.η f.X.B
        εYB = AY.counit.η f.Y.B
    in record
      { l = f.l
      ; r = f.r
      ; u = [ f.l , f.r ]₁
      ; d-eq = lemma-delta f
      ; s-eq = lemma-epsilon f
      }
  ; identity = refl , refl , [-,-].identity
  ; homomorphism = refl , refl , [-,-].homomorphism
  ; F-resp-≈ = λ z → z .proj₁ , z .proj₂ , [-,-].F-resp-≈ z
  }

