{-# OPTIONS --without-K --safe #-}

open import Level using (_⊔_)

open import Categories.Category using (Category)

module Categories.Functor.Profunctor.Tabulator {o ℓ e} {C : Category o ℓ e} where
open import Data.Product  
open import Categories.Functor renaming (id to idF)
open import Categories.Functor.Profunctor using (Profunctor)
open import Relation.Binary.Bundles 
open import Function.Equality using (Π; _⟶_; _⟨$⟩_; cong)

private
  module 𝒞 = Category C

open 𝒞

record tab₀ (p : Profunctor C C) : Set (o ⊔ ℓ)
  where
    field
      B : Obj
      ξ : Setoid.Carrier (Functor.F₀ p (B , B))

record tab⇒ (p : Profunctor C C) (x y : tab₀ p) : Set (o ⊔ ℓ ⊔ e) where
  module x = tab₀ x
  module y = tab₀ y
  field
    arr : x.B ⇒ y.B
    eq : Setoid._≈_ (Functor.F₀ p (x.B , y.B))
           (Functor.F₁ p (id , arr) ⟨$⟩ x.ξ)
           (Functor.F₁ p (arr , id) ⟨$⟩ y.ξ)

Tabulator : (p : Profunctor C C) → Category (o ⊔ ℓ) (o ⊔ ℓ ⊔ e) e 
Tabulator p = record
  { Obj = tab₀ p
  ; _⇒_ = λ { s t → tab⇒ p s t }
  ; _≈_ = λ h k → let module h = tab⇒ h
                      module k = tab⇒ k
                    in h.arr ≈ k.arr
  ; id = λ { {A} → let pAA = Functor.F₀ p (tab₀.B A , tab₀.B A) in record 
    { arr = id 
    ; eq = Setoid.refl pAA
    }}
  ; _∘_ = λ { {A} {B} {C} t s → 
    let module t = tab⇒ t
        module s = tab⇒ s
        in record 
          { arr = t.arr ∘ s.arr 
          ; eq = {!  !} 
          } }
  ; assoc = assoc
  ; sym-assoc = sym-assoc
  ; identityˡ = λ { {A} {B} {f} → identityˡ }
  ; identityʳ = λ { {A} {B} {f} → identityʳ }
  ; identity² = λ { {A} → identity² }
  ; equiv = {!  !}
  ; ∘-resp-≈ = ∘-resp-≈
  }
