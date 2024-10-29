{-# OPTIONS --without-K --safe #-}
module Categories.Object.NaturalNumbers.Properties.F-Algebras where

open import Level
open import Function using (_$_)

open import Categories.Category.Core
open import Categories.Category.Construction.F-Algebras using (F-Algebras)
open import Categories.Category.Cocartesian using (BinaryCoproducts)
open import Categories.Category.Cartesian.Bundle using (CartesianCategory)
open import Categories.Category.BinaryProducts using (BinaryProducts)
open import Categories.Functor using (Endofunctor; Functor)
open import Categories.Functor.Algebra using (F-Algebra; F-Algebra-Morphism)
open import Categories.Object.Terminal using (Terminal)
open import Categories.Object.Initial using (Initial; IsInitial)

import Categories.Morphism.Reasoning as MR
import Categories.Object.NaturalNumbers as NNOs
import Categories.Object.NaturalNumbers.Parametrized as PNNO

-- A NNO is an inital algebra for the 'X ↦ ⊤ + X' endofunctor.
module _ {o ℓ e} (𝒞 : Category o ℓ e) (𝒞-Terminal : Terminal 𝒞) (𝒞-Coproducts : BinaryCoproducts 𝒞) where

  open Terminal 𝒞-Terminal
  open BinaryCoproducts 𝒞-Coproducts
  open Category 𝒞
  open HomReasoning
  open Equiv
  open MR 𝒞
  open NNOs 𝒞 𝒞-Terminal

  Maybe : Functor 𝒞 𝒞
  Maybe = record
    { F₀ = λ X → ⊤ + X
    ; F₁ = λ f → [ i₁ , i₂ ∘ f ]
    ; identity = []-cong₂ refl identityʳ ○ +-η 
    ; homomorphism = +-unique (pullʳ inject₁ ○ inject₁) (pullʳ inject₂ ○ pullˡ inject₂ ○ assoc)
    ; F-resp-≈ = λ eq → []-cong₂ refl (∘-resp-≈ʳ eq)
    }

  private
    module Maybe = Functor Maybe

  Initial⇒NNO : Initial (F-Algebras Maybe) → NNO
  Initial⇒NNO initial = record
    { N = ⊥.A
    ; isNNO = record
      { z = ⊥.α ∘ i₁
      ; s = ⊥.α ∘ i₂
      ; universal = λ {A} q f →
        F-Algebra-Morphism.f (initial.! {A = alg q f})
      ; z-commute = λ {A} {q} {f} → begin
        q                                                                 ≈⟨ ⟺ inject₁ ⟩
        [ q , f ] ∘ i₁                                                    ≈⟨ pushʳ (⟺ inject₁) ⟩
        (([ q , f ] ∘ [ i₁ , i₂ ∘ F-Algebra-Morphism.f initial.! ]) ∘ i₁) ≈⟨ pushˡ (⟺ (F-Algebra-Morphism.commutes (initial.! {A = alg q f}))) ⟩
        F-Algebra-Morphism.f initial.! ∘ ⊥.α ∘ i₁                         ∎
      ; s-commute = λ {A} {q} {f} → begin
        (f ∘ F-Algebra-Morphism.f initial.!)                            ≈⟨ pushˡ (⟺ inject₂) ⟩
        [ q , f ] ∘ i₂ ∘ F-Algebra-Morphism.f initial.!                 ≈⟨ pushʳ (⟺ inject₂) ⟩
        ([ q , f ] ∘ [ i₁ , i₂ ∘ F-Algebra-Morphism.f initial.! ]) ∘ i₂ ≈⟨ pushˡ (⟺ (F-Algebra-Morphism.commutes (initial.! {A = alg q f}))) ⟩
        F-Algebra-Morphism.f initial.! ∘ ⊥.α ∘ i₂                       ∎
      ; unique = λ {A} {f} {q} {u} eqᶻ eqˢ → ⟺ $ initial.!-unique record
          { f = u
          ; commutes = begin
            u ∘ ⊥.α ≈⟨ ⟺ +-g-η ⟩
            [ (u ∘ ⊥.α) ∘ i₁ , (u ∘ ⊥.α) ∘ i₂ ] ≈⟨ []-cong₂ (assoc ○ ⟺ eqᶻ) (assoc ○ ⟺ eqˢ) ⟩
            [ f , q ∘ u ]                       ≈⟨ +-unique (pullʳ inject₁ ○ inject₁) (pullʳ inject₂ ○ pullˡ inject₂) ⟩
            [ f , q ] ∘ [ i₁ , i₂ ∘ u ]         ∎
          }
      }
    }
    where
      module initial = Initial initial
      module ⊥ = F-Algebra initial.⊥
  
      alg : ∀ {A} → (q : ⊤ ⇒ A) → (f : A ⇒ A) → F-Algebra Maybe
      alg {A} q f = record
        { A = A
        ; α = [ q , f ]
        }

  NNO⇒Initial : NNO → Initial (F-Algebras Maybe)
  NNO⇒Initial nno = record
    { ⊥ = record
      { A = N 
      ; α = [ z , s ]
      }
    ; ⊥-is-initial = record
      { ! = λ {alg} → record
        { f = universal (F-Algebra.α alg ∘ i₁) (F-Algebra.α alg ∘ i₂)
        ; commutes = begin
          universal (F-Algebra.α alg ∘ i₁) (F-Algebra.α alg ∘ i₂) ∘ [ z , s ]                                         ≈⟨ ∘-distribˡ-[] ⟩
          [ universal (F-Algebra.α alg ∘ i₁) (F-Algebra.α alg ∘ i₂) ∘ z 
          , universal (F-Algebra.α alg ∘ i₁) (F-Algebra.α alg ∘ i₂) ∘ s ]                                             ≈⟨ []-cong₂ (⟺ z-commute) (⟺ s-commute ○ assoc) ⟩
          [ F-Algebra.α alg ∘ i₁ , F-Algebra.α alg ∘ (i₂ ∘ universal (F-Algebra.α alg ∘ i₁) (F-Algebra.α alg ∘ i₂)) ] ≈˘⟨ ∘-distribˡ-[] ⟩
          F-Algebra.α alg ∘ [ i₁ , i₂ ∘ universal (F-Algebra.α alg ∘ i₁) (F-Algebra.α alg ∘ i₂) ]                     ∎
        }
      ; !-unique = λ {A} f →
        let z-commutes = begin
              F-Algebra.α A ∘ i₁                                          ≈⟨ pushʳ (⟺ inject₁) ⟩
              (F-Algebra.α A ∘ [ i₁ , i₂ ∘ F-Algebra-Morphism.f f ]) ∘ i₁ ≈˘⟨ F-Algebra-Morphism.commutes f ⟩∘⟨refl ⟩
              (F-Algebra-Morphism.f f ∘ [ z , s ]) ∘ i₁                   ≈⟨ pullʳ inject₁ ⟩
              F-Algebra-Morphism.f f ∘ z                                  ∎
            s-commutes = begin
              (F-Algebra.α A ∘ i₂) ∘ F-Algebra-Morphism.f f               ≈⟨ pullʳ (⟺ inject₂) ○ ⟺ assoc ⟩
              (F-Algebra.α A ∘ [ i₁ , i₂ ∘ F-Algebra-Morphism.f f ]) ∘ i₂ ≈˘⟨ F-Algebra-Morphism.commutes f ⟩∘⟨refl ⟩
              (F-Algebra-Morphism.f f ∘ [ z , s ]) ∘ i₂                   ≈⟨ pullʳ inject₂ ⟩
              F-Algebra-Morphism.f f ∘ s                                  ∎
        in ⟺ $ unique z-commutes s-commutes
      }
    }
    where
      open NNO nno

-- A parametrized NNO corresponds to existence of a Maybe algebra and initiality of the PNNO algebra
module _ {o ℓ e} (CC : CartesianCategory o ℓ e) (𝒞-Coproducts : BinaryCoproducts (CartesianCategory.U CC)) where
  open CartesianCategory CC renaming (U to 𝒞)
  open BinaryCoproducts 𝒞-Coproducts
  open BinaryProducts products hiding (unique)
  open HomReasoning
  open Equiv
  open MR 𝒞
  open PNNO CC
  open NNOs 𝒞 terminal
  open Terminal terminal

  coproductF : Obj → Endofunctor 𝒞
  coproductF A = record
    { F₀ = λ X → A + X
    ; F₁ = λ f → [ i₁ , (i₂ ∘ f) ]
    ; identity = λ {A} → trans ([]-congˡ identityʳ) 
                               (coproduct.unique identityˡ identityˡ) 
    ; homomorphism = λ {X} {Y} {Z} {f} {g} → coproduct.unique 
      (trans (pullʳ inject₁) (inject₁)) 
      (trans (pullʳ inject₂) (trans (pullˡ inject₂) assoc))
    ; F-resp-≈ = λ fg → []-congˡ (∘-resp-≈ʳ fg)
    }

  private
    module coproductF A = Functor (coproductF A)

  -- the algebra that corresponds to a PNNO (if it is initial)
  PNNO-Algebra : ∀ A N → ⊤ ⇒ N → N ⇒ N → F-Algebra (coproductF A)
  PNNO-Algebra A N z s = record
    { A = A × N
    ; α = [ ⟨ id , z ∘ ! ⟩ , id ⁂ s ] 
    }

  Initial⇒PNNO : (algebra : F-Algebra (Maybe 𝒞 terminal 𝒞-Coproducts)) 
    → (∀ A → IsInitial (F-Algebras (coproductF A)) 
                       (PNNO-Algebra A (F-Algebra.A algebra) (F-Algebra.α algebra ∘ i₁) (F-Algebra.α algebra ∘ i₂))) 
    → ParametrizedNNO
  Initial⇒PNNO algebra isInitial = record 
    { N = N
    ; isParametrizedNNO = record
      { z = z
      ; s = s
      ; universal = λ {A} {X} f g → F-Algebra-Morphism.f (isInitial.! A {A = alg′ f g})
      ; commute₁ = λ {A} {X} {f} {g} → begin 
        f                                                                          ≈˘⟨ inject₁ ⟩ 
        [ f , g ] ∘ i₁                                                             ≈⟨ pushʳ (⟺ inject₁) ⟩
        (([ f , g ] ∘ [ i₁ , i₂ ∘ F-Algebra-Morphism.f (isInitial.! A) ]) ∘ i₁)    ≈⟨ pushˡ (⟺ (F-Algebra-Morphism.commutes (isInitial.! A {A = alg′ f g}))) ⟩
        (F-Algebra-Morphism.f (isInitial.! A) ∘ [ ⟨ id , z ∘ ! ⟩ , id ⁂ s ] ∘  i₁) ≈⟨ refl⟩∘⟨ inject₁ ⟩
        (F-Algebra-Morphism.f (IsInitial.! (isInitial A))) ∘ ⟨ id , z ∘ ! ⟩        ∎
      ; commute₂ = λ {A} {X} {f} {g} → begin 
        g ∘ F-Algebra-Morphism.f (IsInitial.! (isInitial A))                                ≈⟨ pushˡ (⟺ inject₂) ⟩ 
        [ f , g ] ∘ i₂ ∘ F-Algebra-Morphism.f (IsInitial.! (isInitial A))                   ≈⟨ pushʳ (⟺ inject₂) ⟩
        (([ f , g ] ∘ [ i₁ , i₂ ∘ F-Algebra-Morphism.f (IsInitial.! (isInitial A)) ]) ∘ i₂) ≈⟨ pushˡ (⟺ (F-Algebra-Morphism.commutes (isInitial.! A {A = alg′ f g}))) ⟩
        (F-Algebra-Morphism.f (isInitial.! A) ∘ [ ⟨ id , z ∘ ! ⟩ , id ⁂ s ] ∘  i₂)          ≈⟨ (refl⟩∘⟨ inject₂) ⟩
        F-Algebra-Morphism.f (IsInitial.! (isInitial A)) ∘ (id ⁂ s)                         ∎
      ; unique = λ {A} {X} {f} {g} {u} eqᶻ eqˢ → ⟺ $ isInitial.!-unique A {A = alg′ f g} (record 
        { f = u 
        ; commutes = begin 
          u ∘ [ ⟨ id , z ∘ ! ⟩ , id ⁂ s ]              ≈⟨ ⟺ +-g-η ⟩ 
          [ ((u ∘ [ ⟨ id , z ∘ ! ⟩ , id ⁂ s ]) ∘ i₁) 
          , ((u ∘ [ ⟨ id , z ∘ ! ⟩ , id ⁂ s ]) ∘ i₂) ] ≈⟨ []-cong₂ (pullʳ inject₁) (pullʳ inject₂) ⟩ 
          [ u ∘ ⟨ id , z ∘ ! ⟩ , u ∘ (id ⁂ s) ]        ≈˘⟨ []-cong₂ eqᶻ eqˢ ⟩ 
          [ f , g ∘ u ]                                ≈⟨ +-unique (pullʳ inject₁ ○ inject₁) (pullʳ inject₂ ○ pullˡ inject₂) ⟩ 
          [ f , g ] ∘ [ i₁ , i₂ ∘ u ]                  ∎ 
        })
      } 
    }
    where
      open F-Algebra algebra using (α) renaming (A to N)
      z = α ∘ i₁
      s = α ∘ i₂

      module isInitial A = IsInitial (isInitial A)

      alg′  : ∀ {A X} → (f : A ⇒ X) → (g : X ⇒ X) → F-Algebra (coproductF A)
      alg′ {A} {X} f g = record 
        { A = X 
        ; α = [ f , g ] 
        }

  PNNO⇒Initial₁ : ParametrizedNNO → Initial (F-Algebras (Maybe 𝒞 terminal 𝒞-Coproducts))
  PNNO⇒Initial₁ pnno = (NNO⇒Initial 𝒞 terminal 𝒞-Coproducts) (PNNO⇒NNO pnno)

  PNNO⇒Initial₂ : (pnno : ParametrizedNNO)
    → (∀ A → IsInitial (F-Algebras (coproductF A)) 
                       (PNNO-Algebra A (ParametrizedNNO.N pnno) (ParametrizedNNO.z pnno) (ParametrizedNNO.s pnno)))
  PNNO⇒Initial₂ pnno A = record 
    { ! = λ {alg} → record 
      { f = universal (F-Algebra.α alg ∘ i₁) (F-Algebra.α alg ∘ i₂) 
      ; commutes = begin 
        universal (F-Algebra.α alg ∘ i₁) (F-Algebra.α alg ∘ i₂) ∘ [ ⟨ id , z ∘ ! ⟩ , id ⁂ s ]   ≈⟨ ∘-distribˡ-[] ⟩ 
        [ universal (F-Algebra.α alg ∘ i₁) (F-Algebra.α alg ∘ i₂) ∘ ⟨ id , z ∘ ! ⟩ 
        , universal (F-Algebra.α alg ∘ i₁) (F-Algebra.α alg ∘ i₂) ∘ (id ⁂ s) ]                  ≈⟨ []-cong₂ (⟺ commute₁) (⟺ commute₂) ⟩
        [ F-Algebra.α alg ∘ i₁ 
        , ((F-Algebra.α alg ∘ i₂) ∘ universal (F-Algebra.α alg ∘ i₁) (F-Algebra.α alg ∘ i₂)) ]  ≈˘⟨ trans ∘-distribˡ-[] ([]-congˡ sym-assoc) ⟩
        F-Algebra.α alg ∘ [ i₁ , i₂ ∘ universal (F-Algebra.α alg ∘ i₁) (F-Algebra.α alg ∘ i₂) ] ∎ 
      } 
    ; !-unique = λ {X} f → 
      let commute₁ = begin 
            F-Algebra.α X ∘ i₁                                            ≈⟨ pushʳ (⟺ inject₁) ⟩ 
            ((F-Algebra.α X ∘ [ i₁ , i₂ ∘ F-Algebra-Morphism.f f ]) ∘ i₁) ≈˘⟨ F-Algebra-Morphism.commutes f ⟩∘⟨refl ⟩
            ((F-Algebra-Morphism.f f ∘ [ ⟨ id , z ∘ ! ⟩ , id ⁂ s ]) ∘ i₁) ≈⟨ pullʳ inject₁ ⟩
            F-Algebra-Morphism.f f ∘ ⟨ id , z ∘ ! ⟩                       ∎
          commute₂ = begin 
            (F-Algebra.α X ∘ i₂) ∘ F-Algebra-Morphism.f f                 ≈⟨ (pullʳ (⟺ inject₂) ○ ⟺ assoc) ⟩ 
            ((F-Algebra.α X ∘ [ i₁ , i₂ ∘ F-Algebra-Morphism.f f ]) ∘ i₂) ≈˘⟨ F-Algebra-Morphism.commutes f ⟩∘⟨refl ⟩
            ((F-Algebra-Morphism.f f ∘ [ ⟨ id , z ∘ ! ⟩ , id ⁂ s ]) ∘ i₂) ≈⟨ pullʳ inject₂ ⟩
            F-Algebra-Morphism.f f ∘ (id ⁂ s)                             ∎
      in ⟺ $ unique commute₁ commute₂
    }
    where
      open ParametrizedNNO pnno