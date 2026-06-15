{-# OPTIONS --without-K --safe #-}

open import Level using (_⊔_)

open import Categories.Category using (Category)

module Categories.Functor.Profunctor.Tabulator {o ℓ e} {C : Category o ℓ e} where
open import Data.Product  
open import Categories.Functor renaming (id to idF)
open import Categories.Functor.Profunctor using (Profunctor)
open import Categories.Functor.Bifunctor.Properties
open import Categories.Category.Instance.Setoids
open import Relation.Binary.Bundles 
open import Relation.Binary.Reasoning.Setoid as SetoidR
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
  ; _≈_ = λ h k → 
    let module h = tab⇒ h
        module k = tab⇒ k
        in h.arr ≈ k.arr
  ; id = λ { {A} → 
      let pAA = Functor.F₀ p (tab₀.B A , tab₀.B A) 
      in record 
        { arr = id 
        ; eq = Setoid.refl pAA
        }}
  ; _∘_ = λ { {A} {B} {C} t s → 
    let module t = tab⇒ t
        module s = tab⇒ s
        module A = tab₀ A
        module B = tab₀ B
        module C = tab₀ C
        module p = Functor p
        PAA = p.F₀ (A.B , A.B)
        PBB = p.F₀ (B.B , B.B)
        PCC = p.F₀ (C.B , C.B)
        PAC = p.F₀ (A.B , C.B)
        open SetoidR PAC
        in record 
          { arr = t.arr ∘ s.arr 
          ; eq = {!  !}
            --  SetoidR.begin
            --   p.F₁ (id , t.arr ∘ s.arr) ⟨$⟩ A.ξ
            --     SetoidR.≈⟨ p.homomorphism {f = (id , s.arr)} {g = (id , t.arr)} (Setoid.refl PAA) ⟩
            --   (p.F₁ (id , t.arr) ∘ p.F₁ (id , s.arr)) ⟨$⟩ A.ξ
            --     SetoidR.≈⟨ cong (p.F₁ (id , t.arr)) s.eq ⟩
            --   p.F₁ (id , t.arr) ⟨$⟩ (p.F₁ (s.arr , id) ⟨$⟩ B.ξ)
            --     SetoidR.≈⟨ ? ⟩ -- p-props.[_]-commute {f = s.arr} {g = t.arr} (Setoid.refl PBB) ⟩
            --   p.F₁ (s.arr , id) ⟨$⟩ (p.F₁ (id , t.arr) ⟨$⟩ B.ξ)
            --     SetoidR.≈⟨ cong (p.F₁ (s.arr , id)) t.eq ⟩
            --   p.F₁ (s.arr , id) ⟨$⟩ (p.F₁ (t.arr , id) ⟨$⟩ C.ξ)
            --     SetoidR.≈˘⟨ p.homomorphism {f = (t.arr , id)} {g = (s.arr , id)} (Setoid.refl PCC) ⟩
            --   p.F₁ (t.arr ∘ s.arr , id) ⟨$⟩ C.ξ
            --   SetoidR.∎
          } }
  ; assoc = assoc
  ; sym-assoc = sym-assoc
  ; identityˡ = λ { {A} {B} {f} → identityˡ }
  ; identityʳ = λ { {A} {B} {f} → identityʳ }
  ; identity² = λ { {A} → identity² }
  ; equiv = record 
    { refl = λ {x} → Equiv.refl 
    ; sym = λ x → Equiv.sym x 
    ; trans = λ x y → Equiv.trans x y 
    }
  ; ∘-resp-≈ = ∘-resp-≈
  }
