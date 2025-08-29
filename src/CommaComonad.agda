
open import Categories.Category
open import Categories.Functor renaming (id to idF)
open import Categories.Functor.Properties
open import Categories.Category.Core
module CommaComonad {o l e} where

open import Level
open import Categories.Comonad
open import Categories.Category.Construction.Comma using (CommaObj; Comma⇒; Comma; _↙_;Dom; Cod)

open import Categories.NaturalTransformation using (NaturalTransformation; _∘ˡ_; _∘ʳ_; ntHelper; _∘ᵥ_; id∘F⇒F; F⇒F∘id)
open import Categories.Category.Construction.Arrow

record D1Obj : Set (o ⊔ l) where
  field
    dom cod : Category o l e
    fun : Functor dom cod

--open D1Obj

record D1Mor (s : D1Obj) (t : D1Obj) : Set (o ⊔ l ⊔ e) where 
  module s = D1Obj s 
  module t = D1Obj t 
  field 
    W : Functor s.dom t.dom
    E : Functor s.cod t.cod
    α : NaturalTransformation (E ∘F s.fun) (t.fun ∘F W)

open D1Mor

{-

* --s--> *
|W      E|
|        | 
V        V
* --t--> *
-}

open import Categories.NaturalTransformation.NaturalIsomorphism hiding (_≃_)
open import Categories.NaturalTransformation.Equivalence
open NaturalIsomorphism

record D1Equality {A} {B} (f g : D1Mor A B) : Set {! !} where
  module f = D1Mor f 
  module g = D1Mor g 
  module fα = NaturalTransformation (α f)
  module gα = NaturalTransformation (α g)
  open Category (D1Obj.cod B)
  field
    eq-W : NaturalIsomorphism f.W g.W
    eq-E : NaturalIsomorphism f.E g.E
  module eq-W = NaturalIsomorphism eq-W
  module eq-E = NaturalIsomorphism eq-E
  field
    eq-α : ∀ x → fα.η x ∘ {!eq-W.⇐.η ? !} ≈ {! eq-W.⇒.η x !} ∘ gα.η x

{-
 *  -------> *
|  |        |  |
|  |        |  |
|~ |  ↙α    |~ |
|⇒ |        |⇒ |
|  |        |  |
|  |  ↙β    |  |
V  V        V  V
 *  -------> *

 
-}

𝔻₁ : Category (o ⊔ l) (o ⊔ l ⊔ e) (o ⊔ l ⊔ e)
𝔻₁ = record 
  { Obj = D1Obj 
  ; _⇒_ = D1Mor 
  ; _≈_ = λ { {A} {B} F G → D1Equality F G }
  ; id = λ { {A} → record 
    { W = idF 
    ; E = idF 
    ; α = F⇒F∘id ∘ᵥ id∘F⇒F
    } }
  ; _∘_ = λ { P Q → let module P = D1Mor P in 
    let module Q = D1Mor Q in record 
    { W = P.W ∘F Q.W 
    ; E = P.E ∘F Q.E
    ; α = {! !} 
    } } 
  ; assoc = {! !} 
  ; sym-assoc = {! !} 
  ; identityˡ = {! !} 
  ; identityʳ = {! !} 
  ; identity² = {! !} 
  ; equiv = {! !} 
  ; ∘-resp-≈ = {! !} 
  }

-- cmCmd₀ : (F : Functor A X) → 

cmCmd : Comonad 𝔻₁
cmCmd = record 
  { F = {! !} 
  ; ε = {! !} 
  ; δ = {! !} 
  ; assoc = {! !} 
  ; sym-assoc = {! !} 
  ; identityˡ = {! !} 
  ; identityʳ = {! !} 
  }

{-
D₀ : (G : Functor C D) → Functor (Comma idF G) (Comma idF G)
D₀ G = idF

ε : (G : Functor C D) → NaturalTransformation (Dom idF G ∘F D₀ G) (G ∘F Cod idF G)
ε = {! !}

ι : {X : Category o l e} → Functor X (Arrow X)
ι = {! !}
-}

--δ : (G : Functor C D) → NaturalTransformation (D₀ (D₀ G) ∘F ι) (ι ∘F D₀ G)
--δ = 
--
-- ?

open import Categories.Category.Construction.CoEilenbergMoore

coalgs : Category (o ⊔ l ⊔ e) (o ⊔ l ⊔ e) {! !}
coalgs = CoEilenbergMoore cmCmd

