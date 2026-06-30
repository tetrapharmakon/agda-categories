{-# OPTIONS --without-K --safe --warning=noUserWarning --warning=noUselessPrivate #-}

open import Level using (_⊔_;lift;lower;zero;suc)

open import Data.Product using (Σ;_,_; proj₁; proj₂; _×_)
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

module Categories.Rosen.Incoherent.Core {o ℓ e} {C : Category o ℓ e} {M : Monoidal C} (Cl : Closed M) where

private
  module 𝒞 = Category C

-- open 𝒞
import Reason
open Reason C

import Categories.Morphism.Reasoning as MR

open HomReasoning
open MR

open Closed Cl using ([-,-]; [_,_]₀; [_,-]; [_,_]₁; Hom[-⊗_,-]; Hom[-,[_,-]]; Hom-NI)

module Arr = Categories.Category.Construction.Arrow C

record iMR2 (A B : Obj) : Set (o ⊔ ℓ) where
  constructor ⟪_,_⟫
  field
    f : A ⇒ B
    ϕ : B ⇒ [ A , B ]₀

record iMR2₀ : Set (o ⊔ ℓ) where
  field
    A B : Obj
    ξ : iMR2 A B

record iMR2⇒ (X Y : iMR2₀) : Set (o ⊔ ℓ ⊔ e) where
  module X = iMR2₀ X
  module Y = iMR2₀ Y
  module ξX = iMR2 X.ξ
  module ξY = iMR2 Y.ξ
  field
    l : X.A ⇒ Y.A
    r : X.B ⇒ Y.B
    eqf : r ∘ ξX.f ≈ ξY.f ∘ l
    eqϕ : [ l , id ]₁ ∘ ξY.ϕ ∘ r ≈ [ id , r ]₁ ∘ ξX.ϕ

-- total category of incoherent MR systems
τ[iMR2] : Category (o ⊔ ℓ) (o ⊔ ℓ ⊔ e) e 
τ[iMR2] = record
  { Obj = iMR2₀
  ; _⇒_ = λ s t → iMR2⇒ s t
  ; _≈_ = λ f g → let open iMR2⇒ in f .l ≈ g .l × f .r ≈ g .r
    -- let module f = iMR2⇒ f  
    --     module g = iMR2⇒ g in f.l ≈ g.l × f.r ≈ g.r
  ; id = record 
    { l = id 
    ; r = id 
    ; eqf = sym-id-swap 
    ; eqϕ = id-2 
    }
  ; _∘_ = λ f g → 
    let module f = iMR2⇒ f  
        module g = iMR2⇒ g 
        module Hom  {A} = Functor (appʳ [-,-] A)
        module Hom' {A} = Functor (appˡ [-,-] A)
    in record { l = f.l ∘ g.l 
              ; r = f.r ∘ g.r 
              ; eqf = assoc ○ refl⟩∘⟨ g.eqf ○ rw-2-1 f.eqf ○ assoc 
              ; eqϕ = begin [ f.l ∘ g.l , id ]₁ ∘ f.ξY.ϕ ∘ f.r ∘ g.r             ≈⟨ Hom.homomorphism ⟩∘⟨refl ⟩ 
                            ([ g.l , id ]₁ ∘ [ f.l , id ]₁) ∘ f.ξY.ϕ ∘ f.r ∘ g.r ≈⟨ assoc ⟩ 
                            [ g.l , id ]₁ ∘ [ f.l , id ]₁ ∘ f.ξY.ϕ ∘ f.r ∘ g.r   ≈⟨ refl⟩∘⟨ rw-3-1 f.eqϕ ⟩ 
                            [ g.l , id ]₁ ∘ ([ id , f.r ]₁ ∘ g.ξY.ϕ) ∘ g.r       ≈⟨ refl⟩∘⟨ assoc ⟩ 
                            [ g.l , id ]₁ ∘ [ id , f.r ]₁ ∘ g.ξY.ϕ ∘ g.r         ≈⟨ sym-assoc ○ Equiv.sym [ [-,-] ]-commute ⟩∘⟨refl ⟩ 
                            ([ id , f.r ]₁ ∘ [ g.l , id ]₁) ∘ g.ξY.ϕ ∘ g.r       ≈⟨ assoc ○ refl⟩∘⟨ g.eqϕ ⟩ 
                            [ id , f.r ]₁ ∘ [ id , g.r ]₁ ∘ g.ξX.ϕ               ≈⟨ pullˡ C (Equiv.sym Hom'.homomorphism) ⟩ 
                            [ id , f.r ∘ g.r ]₁ ∘ g.ξX.ϕ ∎ 
    }
  ; assoc = λ { {A} {B} {C} {D} {f} {g} {h} → 
    ( assoc {f = iMR2⇒.l f} {g = iMR2⇒.l g} {h = iMR2⇒.l h}) 
    , (assoc {f = iMR2⇒.r f} {g = iMR2⇒.r g} {h = iMR2⇒.r h}) } -- assoc , assoc
  ; sym-assoc = λ { {A} {B} {C} {D} {f} {g} {h} → 
    ( sym-assoc {f = iMR2⇒.l f} {g = iMR2⇒.l g} {h = iMR2⇒.l h}) 
    , (sym-assoc {f = iMR2⇒.r f} {g = iMR2⇒.r g} {h = iMR2⇒.r h}) } -- sym-assoc , sym-assoc 
  ; identityˡ = λ { {A} {B} {f} → identityˡ {f = iMR2⇒.l f} 
                  , identityˡ {f = iMR2⇒.r f} 
                  } -- identityˡ , identityˡ 
  ; identityʳ = λ { {A} {B} {f} → identityʳ {f = iMR2⇒.l f} 
                  , identityʳ {f = iMR2⇒.r f} 
                  } -- identityʳ , identityʳ 
  ; identity² = identity² , identity² 
  ; equiv = record 
    { refl = refl , refl 
    ; sym = λ x → (sym (proj₁ x)) , (sym (proj₂ x)) 
    ; trans = λ eq eq' → (trans (proj₁ eq) (proj₁ eq')) , (trans (proj₂ eq) (proj₂ eq')) 
    }
  ; ∘-resp-≈ = λ eq eq' → (∘-resp-≈ (proj₁ eq) (proj₁ eq')) , (∘-resp-≈ (proj₂ eq) (proj₂ eq'))
  }

-- iMR2 (_ , B) è funtoriale per ogni B fissato; C^op --> Setoids
-- iMR2 (A , _) induce un *profuntore* tra iMR2(A,B) e iMR2(A, B')...

{-

-}

record iMR2ᴸ₀ (B : Obj) : Set (o ⊔ ℓ ⊔ e) where
  field
    A : Obj
    ξ : iMR2 A B 

record iMR2ᴸ⇒ {B : Obj} (X Y : iMR2ᴸ₀ B) : Set (o ⊔ ℓ ⊔ e) where
  module X = iMR2ᴸ₀ X
  module Y = iMR2ᴸ₀ Y   
  module ξX = iMR2 X.ξ  
  module ξY = iMR2 Y.ξ
  field
    u : X.A ⇒ Y.A
    eqf : ξX.f ≈ ξY.f ∘ u
    eqϕ : ξX.ϕ ≈ [ u , id ]₁ ∘ ξY.ϕ

-- funtoriale
iMR2ᴸ : (B : Obj) → Category (o ⊔ ℓ ⊔ e) (o ⊔ ℓ ⊔ e) e
iMR2ᴸ B = record
  { Obj = iMR2ᴸ₀ B
  ; _⇒_ = λ X Y → iMR2ᴸ⇒ {B} X Y
  ; _≈_ = λ p q → let module p = iMR2ᴸ⇒ p 
                      module q = iMR2ᴸ⇒ q
                  in p.u ≈ q.u
  ; id = record 
    { u = id 
    ; eqf = sym-id-1 
    ; eqϕ = Equiv.sym (cancel (Functor.identity [-,-])) 
    }
  ; _∘_ = λ p q → 
    let module p = iMR2ᴸ⇒ p 
        module q = iMR2ᴸ⇒ q
    in record 
      { u = p.u ∘ q.u 
      ; eqf = q.eqf ∙ rw-1-2 p.eqf 
      ; eqϕ = let module Hom = Functor [-,-]
                  module Hom[1-] {A} = Functor (appˡ [-,-] A)
                  module Hom[-1] {A} = Functor (appʳ [-,-] A) 
              in Equiv.sym (begin [ p.u ∘ q.u , id ]₁ ∘ p.ξY.ϕ ≈⟨ pushˡ C Hom[-1].homomorphism ⟩ 
                                  [ q.u , id ]₁ ∘ [ p.u , id ]₁ ∘ p.ξY.ϕ ≈⟨ Equiv.sym (refl⟩∘⟨ p.eqϕ) ⟩ 
                                  [ q.u , id ]₁ ∘ q.ξY.ϕ ≈⟨ Equiv.sym q.eqϕ ⟩ 
                                  q.ξX.ϕ ∎)
      }
  ; assoc = assoc
  ; sym-assoc = sym-assoc
  ; identityˡ = identityˡ
  ; identityʳ = identityʳ
  ; identity² = identity²
  ; equiv = record { refl = refl ; sym = sym ; trans = trans }
  ; ∘-resp-≈ = λ eq eq' → ∘-resp-≈ eq eq'
  }


record iMR2ᴿ₀ (A : Obj) : Set (o ⊔ ℓ ⊔ e) where
  field
    B : Obj
    ξ : iMR2 A B 

record iMR2ᴿ⇒ {A : Obj} (X Y : iMR2ᴿ₀ A) : Set (o ⊔ ℓ ⊔ e) where
  module X = iMR2ᴿ₀ X
  module Y = iMR2ᴿ₀ Y   
  module ξX = iMR2 X.ξ  
  module ξY = iMR2 Y.ξ
  field
    v : X.B ⇒ Y.B
    eqf : v ∘ ξX.f ≈ ξY.f
    eqϕ : [ id , v ]₁ ∘ ξX.ϕ ≈ ξY.ϕ ∘ v

iMR2ᴿ : (A : Obj) → Category (o ⊔ ℓ ⊔ e) (o ⊔ ℓ ⊔ e) e
iMR2ᴿ A = record
  { Obj = iMR2ᴿ₀ A
  ; _⇒_ = λ X Y → iMR2ᴿ⇒ {A} X Y
  ; _≈_ = λ p q → let module p = iMR2ᴿ⇒ p 
                      module q = iMR2ᴿ⇒ q
                  in p.v ≈ q.v
  ; id = record 
    { v = id 
    ; eqf = id-0 
    ; eqϕ = Equiv.trans (cancel (Functor.identity [-,-])) (sym-id-1) }
  ; _∘_ = λ p q → 
    let module p = iMR2ᴿ⇒ p 
        module q = iMR2ᴿ⇒ q
    in record 
      { v = p.v ∘ q.v
      ; eqf = pullʳ C q.eqf ∙ p.eqf 
      ; eqϕ = let module Hom = Functor [-,-]
                  module Hom[1-] {A} = Functor (appˡ [-,-] A)
                  module Hom[-1] {A} = Functor (appʳ [-,-] A) 
              in (begin [ id , p.v ∘ q.v ]₁ ∘ q.ξX.ϕ ≈⟨ pushˡ C Hom[1-].homomorphism ⟩  
                        [ id , p.v ]₁ ∘ [ id , q.v ]₁ ∘ q.ξX.ϕ ≈⟨ refl⟩∘⟨ q.eqϕ ⟩  
                        [ id , p.v ]₁ ∘ q.ξY.ϕ ∘ q.v ≈⟨ rw-2-1 p.eqϕ ∙ assoc ⟩  
                        p.ξY.ϕ ∘ p.v ∘ q.v ∎) 
      }
  ; assoc = assoc
  ; sym-assoc = sym-assoc
  ; identityˡ = identityˡ
  ; identityʳ = identityʳ
  ; identity² = identity²
  ; equiv = record { refl = refl ; sym = sym ; trans = trans }
  ; ∘-resp-≈ = λ eq eq' → ∘-resp-≈ eq eq'
  }

private
 variable
  A A' B B' : Obj

left : (u : A ⇒ A') → Functor (iMR2ᴿ A') (iMR2ᴿ A)
left {A} {A'} u = record
  { F₀ = λ { x → 
    let module x = iMR2ᴿ₀ x 
    in record 
    { B = x.B
    ; ξ = ⟪ iMR2.f x.ξ ∘ u , [ u , id ]₁ ∘ iMR2.ϕ x.ξ ⟫ 
    }}
  ; F₁ = λ { {x} {y} f → 
      let module x   = iMR2ᴿ₀ x
          module ξx  = iMR2 x.ξ
          module y   = iMR2ᴿ₀ y
          module ξy  = iMR2 y.ξ
          module f = iMR2ᴿ⇒ f 
      in record 
    { v = f.v
    ; eqf = begin f.v ∘ f.ξX.f ∘ u   ≈⟨ sym-assoc ⟩ 
                  (f.v ∘ f.ξX.f) ∘ u ≈⟨ f.eqf ⟩∘⟨refl ⟩ 
                  f.ξY.f ∘ u         ∎
    ; eqϕ = begin [ id , f.v ]₁ ∘ [ u , id ]₁ ∘ f.ξX.ϕ ≈⟨ sym-assoc ∙ ([ [-,-] ]-commute ⟩∘⟨refl) ∙ assoc ⟩
                  [ u , id ]₁ ∘ [ id , f.v ]₁ ∘ f.ξX.ϕ ≈⟨ (refl⟩∘⟨ f.eqϕ) ∙ sym-assoc ⟩ 
                  ([ u , id ]₁ ∘ f.ξY.ϕ) ∘ f.v ∎
    }}
  ; identity = λ {A} → refl
  ; homomorphism = λ {X} {Y} {Z} {f} {g} → refl
  ; F-resp-≈ = λ x → x
  }


-- wrong : (v : B ⇒ B') → Functor (iMR2ᴸ B) (iMR2ᴸ B')
-- wrong v = record
--   { F₀ = λ x → 
--   let module x = iMR2ᴸ₀ x 
--       module ξx = iMR2 x.ξ
--   in record 
--    { A = x.A 
--    ; ξ = ⟪ v ∘ ξx.f , {!  !} ⟫ 
--    }
--   ; F₁ = {!  !}
--   ; identity = {!  !}
--   ; homomorphism = {!  !}
--   ; F-resp-≈ = {!  !}
--   }

right : (v : B ⇒ B') → Bifunctor (Category.op (iMR2ᴸ B)) (iMR2ᴸ B') (Setoids (ℓ ⊔ e) e)
right v = record
  { F₀ = λ {(x , y) → 
     let module x  = iMR2ᴸ₀ x 
         module ξx = iMR2 x.ξ
         module y  = iMR2ᴸ₀ y 
         module ξy = iMR2 y.ξ
     in record
       { Carrier = Σ (x.A ⇒ y.A) (λ u →
           (v ∘ ξx.f ≈ ξy.f ∘ u)
         × ([ id , v ]₁ ∘ ξx.ϕ ≈ [ u , id ]₁ ∘ ξy.ϕ ∘ v))
       ; _≈_ = λ p q → proj₁ p ≈ proj₁ q
       ; isEquivalence = record { refl = refl ; sym = sym ; trans = trans }
       }}
  ; F₁ = λ { {(x , y)} {(x' , y')} (s , t) →
      let module x   = iMR2ᴸ₀ x
          module ξx  = iMR2 x.ξ
          module x'  = iMR2ᴸ₀ x'
          module ξx' = iMR2 x'.ξ
          module y   = iMR2ᴸ₀ y
          module ξy  = iMR2 y.ξ
          module y'  = iMR2ᴸ₀ y'
          module ξy' = iMR2 y'.ξ
          module s   = iMR2ᴸ⇒ s
          module t   = iMR2ᴸ⇒ t
          module Hom[-1] {A} = Functor (appʳ [-,-] A)
      in record
      { _⟨$⟩_ = λ { (u , (eqf , eqϕ)) →
          let u' : x'.A ⇒ y'.A
              u' = t.u ∘ u ∘ s.u
              eqf' : v ∘ ξx'.f ≈ ξy'.f ∘ u'
              eqf' = begin
                v ∘ ξx'.f                   ≈⟨ (refl⟩∘⟨ s.eqf) ∙ sym-assoc ⟩
                (v ∘ ξx.f) ∘ s.u            ≈⟨ rw eqf ∙ assoc ⟩
                ξy.f ∘ (u ∘ s.u)            ≈⟨ rw t.eqf ∙ assoc ⟩
                ξy'.f ∘ (t.u ∘ (u ∘ s.u))   ∎
              eqϕ' : [ id , v ]₁ ∘ ξx'.ϕ ≈ [ u' , id ]₁ ∘ ξy'.ϕ ∘ v
              eqϕ' = begin
                [ id , v ]₁ ∘ ξx'.ϕ                               ≈⟨ (refl⟩∘⟨ s.eqϕ) ∙ sym-assoc ⟩
                ([ id , v ]₁ ∘ [ s.u , id ]₁) ∘ ξx.ϕ              ≈⟨ (rw [ [-,-] ]-commute) ∙ assoc ⟩
                [ s.u , id ]₁ ∘ ([ id , v ]₁ ∘ ξx.ϕ)              ≈⟨ (refl⟩∘⟨ eqϕ) ∙ sym-assoc ⟩
                ([ s.u , id ]₁ ∘ [ u , id ]₁) ∘ (ξy.ϕ ∘ v)        ≈⟨ rw (Equiv.sym Hom[-1].homomorphism) ⟩
                [ u ∘ s.u , id ]₁ ∘ (ξy.ϕ ∘ v)                    ≈⟨ skip (rw t.eqϕ) ∙ sym-assoc ∙ (sym-assoc ⟩∘⟨refl) ∙ assoc ⟩
                ([ u ∘ s.u , id ]₁ ∘ [ t.u , id ]₁) ∘ (ξy'.ϕ ∘ v) ≈⟨ rw (Equiv.sym Hom[-1].homomorphism) ⟩
                [ t.u ∘ u ∘ s.u , id ]₁ ∘ (ξy'.ϕ ∘ v)             ∎
          in (u' , (eqf' , eqϕ')) }
  ; cong = λ { {p} {q} p≈q → skip (rw p≈q) }
  } }
  ; identity = λ { {(x , y)} {p} {q} p≈q →
      let u  = proj₁ p
          u' = proj₁ q
      in begin
        id ∘ u ∘ id  ≈⟨ identityˡʳ ⟩
        u            ≈⟨ p≈q ⟩
        u'           ∎ }
  ; homomorphism = λ { {(x , y)} {(x' , y')} {(x'' , y'')} {(s , t)} {(s' , t')} {p} {q} p≈q →
      let module s  = iMR2ᴸ⇒ s
          module t  = iMR2ᴸ⇒ t
          module s' = iMR2ᴸ⇒ s'
          module t' = iMR2ᴸ⇒ t'
          u  = proj₁ p
          u' = proj₁ q
      in begin
        (t'.u ∘ t.u) ∘ (u ∘ (s.u ∘ s'.u))  ≈⟨ skip (rw p≈q) ∙ assoc ⟩
        t'.u ∘ (t.u ∘ (u' ∘ (s.u ∘ s'.u))) ≈⟨ skip (skip sym-assoc ∙ sym-assoc) ⟩
        t'.u ∘ ((t.u ∘ (u' ∘ s.u)) ∘ s'.u) ∎ }
  ; F-resp-≈ = λ { (s≈s' , t≈t') p≈q → replace-3 t≈t' p≈q s≈s' }
  }
