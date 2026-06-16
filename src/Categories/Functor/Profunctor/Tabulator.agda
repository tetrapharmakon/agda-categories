{-# OPTIONS --without-K --safe #-}

open import Level using (_⊔_;lift;zero;suc)

open import Categories.Category using (Category)

module Categories.Functor.Profunctor.Tabulator {o ℓ e} {C : Category o ℓ e} where
open import Data.Product  
open import Categories.Functor renaming (id to idF)
open import Categories.Functor.Profunctor using (Profunctor)
open import Categories.Functor.Bifunctor.Properties
open import Categories.Category.Instance.Setoids
open import Relation.Binary.Bundles 
import Relation.Binary.Reasoning.Setoid as SetoidR
open import Function.Equality using (Π; _⟶_; _⟨$⟩_; cong) renaming (_∘_ to _∗_)

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
        p₀ = p
        module p = Functor p₀
        PAA = p.F₀ (A.B , A.B)
        PBB = p.F₀ (B.B , B.B)
        PCC = p.F₀ (C.B , C.B)
        PAC = p.F₀ (A.B , C.B)
        open SetoidR PAC
        in record 
          { arr = t.arr ∘ s.arr 
          ; eq = begin
              p.F₁ (id , t.arr ∘ s.arr) ⟨$⟩ A.ξ                  ≈⟨ Setoid.sym PAC (p.F-resp-≈ (identity² , Equiv.refl) (Setoid.refl PAA)) ⟩
              p.F₁ (id ∘ id , t.arr ∘ s.arr) ⟨$⟩ A.ξ             ≈⟨ p.homomorphism (Setoid.refl PAA) ⟩
              p.F₁ (id , t.arr) ⟨$⟩ (p.F₁ (id , s.arr) ⟨$⟩ A.ξ)  ≈⟨ cong (p.F₁ (id , t.arr)) s.eq ⟩
              p.F₁ (id , t.arr) ⟨$⟩ (p.F₁ (s.arr , id) ⟨$⟩ B.ξ)  ≈⟨ Setoid.sym PAC (p.homomorphism (Setoid.refl PBB)) ⟩
              p.F₁ (s.arr ∘ id , t.arr ∘ id) ⟨$⟩ B.ξ             ≈⟨ p.F-resp-≈ (identityʳ , identityʳ) (Setoid.refl PBB) ⟩
              p.F₁ (s.arr , t.arr) ⟨$⟩ B.ξ                       ≈⟨ Setoid.sym PAC (p.F-resp-≈ (identityʳ , identityʳ) (Setoid.refl PBB)) ⟩
              p.F₁ (s.arr ∘ id , t.arr ∘ id) ⟨$⟩ B.ξ             ≈⟨ p.homomorphism {f = (s.arr , id)} {g = (id , t.arr)} (Setoid.refl PBB) ⟩
              (p.F₁ (id , t.arr) ∗ p.F₁ (s.arr , id)) ⟨$⟩ B.ξ    ≈⟨ [ p₀ ]-commute (Setoid.refl PBB) ⟩
              (p.F₁ (s.arr , id) ∗ p.F₁ (id , t.arr)) ⟨$⟩ B.ξ    ≈⟨ Setoid.refl PAC ⟩
              p.F₁ (s.arr , id) ⟨$⟩ (p.F₁ (id , t.arr) ⟨$⟩ B.ξ)  ≈⟨ cong (p.F₁ (s.arr , id)) t.eq ⟩
              p.F₁ (s.arr , id) ⟨$⟩ (p.F₁ (t.arr , id) ⟨$⟩ C.ξ)  ≈⟨ Setoid.sym PAC (p.homomorphism (Setoid.refl PCC)) ⟩
              p.F₁ (t.arr ∘ s.arr , id ∘ id) ⟨$⟩ C.ξ             ≈⟨ p.F-resp-≈ (Equiv.refl , identity²) (Setoid.refl PCC) ⟩
              p.F₁ (t.arr ∘ s.arr , id) ⟨$⟩ C.ξ                  ∎
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


module _ {p : Profunctor C C} where
  
  projection : Functor (Tabulator p) C
  projection = record
    { F₀ = λ {x → let module x = tab₀ x in x.B }
    ; F₁ = λ {f → let module f = tab⇒ f in f.arr }
    ; identity = λ {A} → Equiv.refl
    ; homomorphism = Equiv.refl
    ; F-resp-≈ = λ x → x
    }
  
  projection' : Functor (Tabulator p) C
  projection' = record
    { F₀ = λ {x → let module x = tab₀ x in x.B }
    ; F₁ = λ {f → let module f = tab⇒ f in f.arr }
    ; identity = λ {A} → Equiv.refl
    ; homomorphism = Equiv.refl
    ; F-resp-≈ = λ x → x
    }
  
  open import Categories.Functor.Hom using (Hom[_][-,-])
  open import Categories.NaturalTransformation renaming (id to idN)
  open import Categories.Category.Product using (_⁂_)
  open import Categories.Functor.Construction.LiftSetoids using (LiftSetoids)

  
  cell : NaturalTransformation Hom[ Tabulator p ][-,-] ((LiftSetoids (o ⊔ e) zero ∘F p) ∘F (Functor.op projection' ⁂ projection))
  cell = ntHelper (record 
    { η = λ {(X , Y) → let module X = tab₀ X 
                           module Y = tab₀ Y 
                           module p = Functor p in record 
      { _⟨$⟩_ = λ {u → lift (p.F₁ (id , tab⇒.arr u) ⟨$⟩ X.ξ) }
      ; cong = λ { i≈j → lift (cong {!  !} i≈j) }
      } }
    ; commute = λ { {(x , x')} {(y , y')} f {t} {t'} h → 
        let module x = tab₀ x 
            module y = tab₀ y 
            module x' = tab₀ x'
            module y' = tab₀ y'
            module p = Functor p in {!  !} }
    })