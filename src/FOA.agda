
{-# OPTIONS --without-K --safe #-}

open import Categories.Category
open import Categories.Category.Core 
open import Categories.Functor
open import Categories.Category.Product
open import Categories.Category.Construction.Functors

module FOA {o ℓ e o' ℓ' e'} {𝓐 : Category o ℓ e} {𝓧 : Category o' ℓ' e'} {F : Functor 𝓐 (Functors 𝓧 𝓧)} where

open import Level

open import Data.Product using (_,_; _×_)
open import Categories.Adjoint
open import Categories.Functor.Algebra
open import Categories.Category.Construction.F-Algebras
open import Categories.NaturalTransformation using (NaturalTransformation; ntHelper)
open import Categories.NaturalTransformation.NaturalIsomorphism.Functors

import Categories.Morphism.Reasoning as MR
-- open import BetterReasoning 𝓧

open Functor
module F = Functor F
  
record FOA-objects : Set (o ⊔ o' ⊔ ℓ') where
    constructor ⟦_,_⟧
    field
        𝕌 : Category.Obj 𝓐
        alg : F-Algebra (F.F₀ 𝕌)

open FOA-objects

open F-Algebra
open F-Algebra-Morphism
open NaturalTransformation
open Category 𝓐

reindex : {A' : Category.Obj 𝓐} (E : FOA-objects) (u : A' ⇒ 𝕌 E) → F-Algebra (F.F₀ A')
reindex E u = record 
  { A = A (alg E) 
  ; α = α (alg E) C.∘ η (F₁ F u) (A (alg E))
  } where module C = Category 𝓧

syntax reindex E u = u ̂* E

record FOA-arrows (E E' : FOA-objects) : Set (ℓ ⊔ ℓ' ⊔ e ⊔ e') where
    constructor ⟅_,_⟆
    field
        p⇒ : 𝕌 E ⇒ 𝕌 E'
        c⇒ : F-Algebra-Morphism (alg E) (p⇒ ̂* E')

open FOA-arrows

FOA : Category (o ⊔ o' ⊔ ℓ') (ℓ ⊔ e ⊔ ℓ' ⊔ e') (e ⊔ e') 
FOA = record
  { Obj = FOA-objects
  ; _⇒_ = λ E E' → FOA-arrows E E'
  ; _≈_ = λ {E} {E'} s t → (p⇒ s P.≈ p⇒ t) × (f (c⇒ s) C.≈ f (c⇒ t))
  ; id = λ { {E} → record 
    { p⇒ = P.id 
    ; c⇒ = record 
      { f = C.id 
      ; commutes = let open C.HomReasoning in 
        C.Equiv.sym 
          (begin _ ≈⟨ (lemma1 E ⟩∘⟨refl)  ⟩ 
                 _ ≈⟨ MR.elimʳ 𝓧 (identity (F.F₀ (𝕌 E))) ⟩ 
                 _ ≈˘⟨ C.identityˡ ⟩ 
                 _ ∎ )
      } 
    } }
  ; _∘_ = λ { {⟦ 𝕌 , alg ⟧} {⟦ param' , alg' ⟧} {⟦ param'' , alg'' ⟧} s t → record 
    { p⇒ = p⇒ s P.∘ p⇒ t 
    ; c⇒ = record 
      { f = f (c⇒ s) C.∘ f (c⇒ t) 
      ; commutes = let open C.HomReasoning in
                   let u  = p⇒ t in 
                   let φ' = f (c⇒ s) in
          begin _ ≈⟨ MR.pullʳ 𝓧 (commutes (c⇒ t)) ○ C.sym-assoc ⟩ 
                _ ≈⟨ (MR.pullˡ 𝓧 (commutes (c⇒ s)) ⟩∘⟨refl) ○ (C.assoc ⟩∘⟨refl) ○ MR.assoc²' 𝓧 ⟩ 
                _ ≈⟨ C.assoc ○ skip-2 (MR.pullˡ 𝓧 (sym-commute (F.F₁ u) φ')) ⟩ 
                _ ≈⟨ (refl⟩∘⟨ C.sym-assoc) ○ (refl⟩∘⟨ (C.sym-assoc ⟩∘⟨refl)) ○  (refl⟩∘⟨ C.assoc) ⟩ 
                _ ≈˘⟨ ((refl⟩∘⟨ C.∘-resp-≈ (homomorphism F) (homomorphism (F.F₀ 𝕌)))) ⟩ 
                _ ≈⟨ C.sym-assoc ⟩ 
                _ ∎ 
      } 
    }}
  ; assoc = P.assoc , C.assoc
  ; sym-assoc = P.sym-assoc , C.sym-assoc
  ; identityˡ = P.identityˡ , C.identityˡ
  ; identityʳ = P.identityʳ , C.identityʳ
  ; identity² = P.identity² , C.identity²
  ; equiv = record 
    { refl = P.Equiv.refl , C.Equiv.refl 
    ; sym = λ {(fst , snd) → P.Equiv.sym fst , C.Equiv.sym snd }
    ; trans = λ {(fst , snd) (fst₁ , snd₁) → 
      P.Equiv.trans fst fst₁ , C.Equiv.trans snd snd₁}
    }
  ; ∘-resp-≈ = λ {(dis , dat) (dis' , dat') → P.∘-resp-≈ dis dis' , C.∘-resp-≈ dat dat'}
  } where module P = Category 𝓐
          module C = Category 𝓧
          open import BetterReasoning 𝓧
          lemma1 : (E : FOA-objects) → α (P.id ̂* E) C.≈ α (alg E) 
          lemma1 E = let open C.HomReasoning in 
            begin _ ≈⟨ MR.elimʳ 𝓧 F.identity ⟩ 
                  _ ∎

open Category.Equiv 


Π : Functor FOA 𝓐 
Π = record
  { F₀ = λ {⟦ 𝕌 , _ ⟧ → 𝕌}
  ; F₁ = λ {⟅ p⇒ , _ ⟆ → p⇒}
  ; identity = refl 𝓐
  ; homomorphism = refl 𝓐
  ; F-resp-≈ = λ (fst , _) → fst
  }

V : Functor FOA 𝓧
V = record
  { F₀ = λ {⟦ 𝕌 , alg ⟧ → A alg}
  ; F₁ = λ {⟅ _ , c⇒ ⟆ → f c⇒ }
  ; identity = refl 𝓧
  ; homomorphism = refl 𝓧
  ; F-resp-≈ = λ (_ , snd) → snd
  }

⟨Π,V⟩ : Functor FOA (Product 𝓐 𝓧)
⟨Π,V⟩ = Π ※ V


open import Categories.Object.Terminal
open import Categories.Object.Initial

open Terminal
open Initial using (⊥; ⊥-id) renaming (! to ¡; !-unique₂ to ⊥unique)

pR : (ch⊤ : Terminal 𝓧) → Functor 𝓐 FOA
pR ch⊤ = record
  { F₀ = λ A → ⟦ A , record { A = ⊤ ch⊤ ; α = ! ch⊤ } ⟧
  ; F₁ = λ f → 
    record { p⇒ = f 
           ; c⇒ = 
            record { f = Category.id 𝓧 
                   ; commutes = !-unique₂ ch⊤ 
                   } 
           }
  ; identity = refl 𝓐 , refl 𝓧
  ; homomorphism = refl 𝓐 , !-unique₂ ch⊤
  ; F-resp-≈ = λ x → x , refl 𝓧
  }

pL : (I : ∀ (A : Category.Obj 𝓐) → Initial (F-Algebras (F.F₀ A))) → 
  Functor 𝓐 FOA
pL I = record
  { F₀ = λ A → ⟦ A , ⊥ (I A) ⟧
  ; F₁ = λ { {A} {A'} u → let ØFA = ¡ (I A) in 
    record 
    { p⇒ = u 
    ; c⇒ = record 
      { f = f ØFA
      ; commutes = commutes ØFA
      } 
    }}
  ; identity = λ { {A} → 
    let α⊥A = α (⊥ (I A)) in 
      refl 𝓐 , ⊥-id (I A) 
        (record { f = f (¡ (I A))
                ; commutes = let open 𝓧.HomReasoning in 
                  commutes (¡ (I A)) ○ rw (MR.elimʳ 𝓧 F.identity)
                }) }
  ; homomorphism = λ { {X} {Y} {Z} {f} {g} → refl 𝓐 , ⊥unique (I X) (¡ (I X)) {!   !} }
  ; F-resp-≈ = λ { {A} {B} {f} {g} x → let open 𝓧.HomReasoning in 
    x , (⊥unique (I A) (¡ (I A)) (¡ (I A)) ○ {!  !})}
  } where module 𝓐 = Category 𝓐
          module 𝓧 = Category 𝓧
          open import BetterReasoning 𝓧

{-
open import Categories.Adjoint

Π⊣pR : (ch⊤ : Terminal 𝓧) → Π ⊣ (pR ch⊤)
Π⊣pR ch⊤ = record 
  { unit = ntHelper (record 
    { η = λ {⟦ 𝕌 , alg ⟧ → record 
      { p⇒ = Category.id 𝓐 
      ; c⇒ = record { f = ! ch⊤ ; commutes = !-unique₂ ch⊤ }
      }}
    ; commute = λ { {⟦ A , X ⟧} {⟦ A' , X' ⟧} _ → MR.id-comm-sym 𝓐 , !-unique₂ ch⊤ }
    })
  ; counit = ntHelper (record 
    { η = λ { _ → Category.id 𝓐 }
    ; commute = λ { _ → MR.id-comm-sym 𝓐 }
    }) 
  ; zig = λ { {⟦ 𝕌 , alg ⟧} → MR.elimʳ 𝓐 P.Equiv.refl }
  ; zag = MR.elimʳ 𝓐 P.Equiv.refl , !-unique₂ ch⊤ 
  } where module P = Category 𝓐
          module C = Category 𝓧

pL⊣p : (I : ∀ (A : Category.Obj 𝓐) → Initial (F-Algebras (F.F₀ A))) → pL I ⊣ Π
pL⊣p I = record 
  { unit = ntHelper (record 
    { η = λ X → Category.id 𝓐 
    ; commute = λ {f → let open P.HomReasoning in 
    id-comm-sym ○ elimʳ P.Equiv.refl ○ introʳ P.Equiv.refl}
    }) 
  ; counit = ntHelper (record 
    { η = λ {⟦ 𝕌 , alg ⟧ → record 
      { p⇒ = Category.id 𝓐 
      ; c⇒ = record 
        { f = f (¡ (I 𝕌)) 
        ; commutes = commutes (¡ (I 𝕌)) 
        } 
      }}
    ; commute = λ { {⟦ UX , ξ ⟧} {⟦ UY , θ ⟧} record { p⇒ = p⇒ ; c⇒ = c⇒ } → let open FOA.HomReasoning in (MR.id-comm-sym 𝓐) , ⊥unique (I UX) {!   !} {!   !} }
    }) 
  ; zig = λ { {A} → MR.elimʳ 𝓐 P.Equiv.refl 
            , let open C.HomReasoning in {!   !}  }
  ; zag = λ {B} → let open P.HomReasoning in 
    MR.elimʳ 𝓐 P.Equiv.refl 
  } where module P = Category 𝓐
          module C  = Category 𝓧
          module FOA = Category FOA
          open MR 𝓐
          open FOA
          module pL = Functor (pL I)
          open F-Algebra-Morphism

Φ : (ph⊥ : Initial 𝓐) → (free : leftAdjointOf (forget (F.F₀ (⊥ ph⊥)))) → Functor 𝓧 FOA
Φ ph⊥ free = record
  { F₀ = λ x → ⟦ ⊥ ph⊥ , F₀ (Ladj free) x ⟧
  ; F₁ = λ { h → record 
    { p⇒ = Category.id 𝓐 
    ; c⇒ = record 
      { f = f (F₁ (Ladj free) h) 
      ; commutes = 
        begin _ ≈⟨ commutes ((F₁ (Ladj free) h)) ⟩ 
              _ ≈˘⟨ (MR.elimʳ 𝓧 (identity F {⊥ ph⊥}) ⟩∘⟨refl) ⟩ 
              _ ∎
      } 
    }}
  ; identity = λ { {A} → refl 𝓐 , identity (Ladj free) {A}}
  ; homomorphism = P.Equiv.sym P.identity² , homomorphism (Ladj free)
  ; F-resp-≈ = λ { {A} {B} {f} {g} x → refl 𝓐 , F-resp-≈ (Ladj free) x}
  } where module P = Category 𝓐
          module C  = Category 𝓧
          module FOA = Category FOA
          open leftAdjointOf
          open C.HomReasoning

{-
                     <--pL---
                       _|_ 
𝓧 ---Φ--> FOA ---Π---> 𝓐
           _|_         _|_
         <--V---     <--pR--- 
-}

Φ⊣V : (ph⊥ : Initial 𝓐) → (free : leftAdjointOf (forget (F.F₀ (⊥ ph⊥)))) → Φ ph⊥ free ⊣ V 
Φ⊣V = {!   !}

-}