{-# OPTIONS --without-K --allow-unsolved-metas #-}

open import Level using (_⊔_;lift;lower;zero;suc)

open import Categories.Category using (Category)

module Categories.Functor.Profunctor.Tabulator {o ℓ e} {C : Category o ℓ e} where
open import Data.Product  
open import Categories.Functor renaming (id to idF)
open import Categories.Functor.Bifunctor using (Bifunctor; appˡ; appʳ)
open import Categories.Functor.Profunctor using (Profunctor)
open import Categories.Functor.Bifunctor.Properties
open import Categories.Category.Instance.Setoids
open import Relation.Binary.Bundles renaming (Setoid to S)
import Relation.Binary.Reasoning.Setoid as SetoidR
open import Function.Equality using (Π; _⟶_; _⟨$⟩_; cong) renaming (_∘_ to _∗_)
open import Categories.Category.Product using (Product;_⁂_)

private
  module 𝒞 = Category C

open 𝒞

record tab₀ (p : Bifunctor (Category.op C) C (Setoids (o ⊔ ℓ ⊔ e) (o ⊔ ℓ ⊔ e))) : Set (o ⊔ ℓ ⊔ e)
  where
    constructor _∣_
    field
      B : Obj
      ξ : S.Carrier (Functor.F₀ p (B , B))

record tab⇒ (p : Bifunctor (Category.op C) C (Setoids (o ⊔ ℓ ⊔ e) (o ⊔ ℓ ⊔ e))) (x y : tab₀ p) : Set (o ⊔ ℓ ⊔ e) where
  constructor _∥_
  module x = tab₀ x
  module y = tab₀ y
  field
    arr : x.B ⇒ y.B
    eq : S._≈_ (Functor.F₀ p (x.B , y.B))
           (Functor.F₁ p (id , arr) ⟨$⟩ x.ξ)
           (Functor.F₁ p (arr , id) ⟨$⟩ y.ξ)

Tabulator : ∀ (p : Bifunctor (Category.op C) C (Setoids (o ⊔ ℓ ⊔ e) (o ⊔ ℓ ⊔ e)))
          → Category (o ⊔ ℓ ⊔ e) (o ⊔ ℓ ⊔ e) e
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
        ; eq = S.refl pAA
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
              p.F₁ (id , t.arr ∘ s.arr) ⟨$⟩ A.ξ                  ≈⟨ S.sym PAC (p.F-resp-≈ (identity² , Equiv.refl) (S.refl PAA)) ⟩
              p.F₁ (id ∘ id , t.arr ∘ s.arr) ⟨$⟩ A.ξ             ≈⟨ p.homomorphism (S.refl PAA) ⟩
              p.F₁ (id , t.arr) ⟨$⟩ (p.F₁ (id , s.arr) ⟨$⟩ A.ξ)  ≈⟨ cong (p.F₁ (id , t.arr)) s.eq ⟩
              p.F₁ (id , t.arr) ⟨$⟩ (p.F₁ (s.arr , id) ⟨$⟩ B.ξ)  ≈⟨ S.sym PAC (p.homomorphism (S.refl PBB)) ⟩
              p.F₁ (s.arr ∘ id , t.arr ∘ id) ⟨$⟩ B.ξ             ≈⟨ p.F-resp-≈ (identityʳ , identityʳ) (S.refl PBB) ⟩
              p.F₁ (s.arr , t.arr) ⟨$⟩ B.ξ                       ≈⟨ S.sym PAC (p.F-resp-≈ (identityʳ , identityʳ) (S.refl PBB)) ⟩
              p.F₁ (s.arr ∘ id , t.arr ∘ id) ⟨$⟩ B.ξ             ≈⟨ p.homomorphism {f = (s.arr , id)} {g = (id , t.arr)} (S.refl PBB) ⟩
              (p.F₁ (id , t.arr) ∗ p.F₁ (s.arr , id)) ⟨$⟩ B.ξ    ≈⟨ [ p₀ ]-commute (S.refl PBB) ⟩
              (p.F₁ (s.arr , id) ∗ p.F₁ (id , t.arr)) ⟨$⟩ B.ξ    ≈⟨ S.refl PAC ⟩
              p.F₁ (s.arr , id) ⟨$⟩ (p.F₁ (id , t.arr) ⟨$⟩ B.ξ)  ≈⟨ cong (p.F₁ (s.arr , id)) t.eq ⟩
              p.F₁ (s.arr , id) ⟨$⟩ (p.F₁ (t.arr , id) ⟨$⟩ C.ξ)  ≈⟨ S.sym PAC (p.homomorphism (S.refl PCC)) ⟩
              p.F₁ (t.arr ∘ s.arr , id ∘ id) ⟨$⟩ C.ξ             ≈⟨ p.F-resp-≈ (Equiv.refl , identity²) (S.refl PCC) ⟩
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


module _ {p : Bifunctor (Category.op C) C (Setoids (o ⊔ ℓ ⊔ e) (o ⊔ ℓ ⊔ e))} where
  
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
  
  open import Categories.Functor.Construction.LiftSetoids using (LiftSetoids)

  
  cell : NaturalTransformation (LiftSetoids zero (o ⊔ ℓ) ∘F Hom[ Tabulator p ][-,-]) (p ∘F (Functor.op projection' ⁂ projection))
  cell = 
    ntHelper (record 
      { η = λ {(X , Y) → let module X = tab₀ X 
                             module Y = tab₀ Y 
                             module p = Functor p in record 
         { _⟨$⟩_ = λ {u → p.F₁ (id , tab⇒.arr (lower u)) ⟨$⟩ X.ξ }
         ; cong = λ { i≈j →
             p.F-resp-≈ (Equiv.refl , lower i≈j) (S.refl (p.F₀ (X.B , X.B)))
           }
         } }
      ; commute = λ { {(x , x')} {(y , y')} f {t} {t'} h → 
          let module x = tab₀ x 
              module y = tab₀ y 
              module x' = tab₀ x'
              module y' = tab₀ y'
              module p = Functor p
              module pL {A} = Functor (appˡ p A)
              module pR {A} = Functor (appʳ p A)
              module t = tab⇒ (lower t)
              module t' = tab⇒ (lower t')
              module f₁ = tab⇒ (proj₁ f)
              module f₂ = tab⇒ (proj₂ f)
              Pyy  = p.F₀ (y.B , y.B)
              Pxx  = p.F₀ (x.B , x.B)
              Pxx' = p.F₀ (x.B , x'.B)
              Pyy' = p.F₀ (y.B , y'.B)
              pf₁f₁ = p.F₀ (f₁.x.B , f₁.x.B)
              open SetoidR Pyy'
              in begin
                p.F₁ (id , f₂.arr ∘ t.arr ∘ f₁.arr) ⟨$⟩ y.ξ                                  ≈⟨ p.F-resp-≈ (Equiv.refl , ∘-resp-≈ʳ (∘-resp-≈ˡ (lower h))) (S.refl Pyy) ⟩
                p.F₁ (id , f₂.arr ∘ t'.arr ∘ f₁.arr) ⟨$⟩ y.ξ                                 ≈⟨ p.F-resp-≈ (Equiv.sym identity² , Equiv.refl) (S.refl pf₁f₁) ⟩
                p.F₁ (id ∘ id , f₂.arr ∘ t'.arr ∘ f₁.arr) ⟨$⟩ y.ξ                            ≈⟨ p.homomorphism (S.refl pf₁f₁) ⟩
                p.F₁ (id , f₂.arr) ⟨$⟩ (p.F₁ (id , t'.arr ∘ f₁.arr) ⟨$⟩ y.ξ)                 ≈⟨ cong (p.F₁ (id , f₂.arr)) (pL.homomorphism (S.refl pf₁f₁)) ⟩
                p.F₁ (id , f₂.arr) ⟨$⟩ (p.F₁ (id , t'.arr) ⟨$⟩ (p.F₁ (id , f₁.arr) ⟨$⟩ y.ξ)) ≈⟨ cong (p.F₁ (id , f₂.arr)) (cong (p.F₁ (id , t'.arr)) f₁.eq) ⟩
                p.F₁ (id , f₂.arr) ⟨$⟩ (p.F₁ (id , t'.arr) ⟨$⟩ (p.F₁ (f₁.arr , id) ⟨$⟩ x.ξ)) ≈⟨ cong (p.F₁ (id , f₂.arr)) ([ p ]-commute (S.refl Pxx)) ⟩
                p.F₁ (id , f₂.arr) ⟨$⟩ (p.F₁ (f₁.arr , id) ⟨$⟩ (p.F₁ (id , t'.arr) ⟨$⟩ x.ξ)) ≈˘⟨ [ p ]-decompose₂ (S.refl Pxx') ⟩
                p.F₁ (f₁.arr , f₂.arr) ⟨$⟩ (p.F₁ (id , t'.arr) ⟨$⟩ x.ξ)
                ∎ }
      })

module _ {p q : Bifunctor (Category.op C) C (Setoids (o ⊔ ℓ ⊔ e) (o ⊔ ℓ ⊔ e))} where


  open import Categories.NaturalTransformation renaming (id to idN)

  h : (α : NaturalTransformation p q) → Functor (Tabulator p) (Tabulator q)
  h α = let module p = Functor p 
            module q = Functor q in 
            record
    { F₀ = λ {x → let module x = tab₀ x 
                      module α = NaturalTransformation α in 
                        record { B = x.B 
                               ; ξ = α.η (x.B , x.B) ⟨$⟩ x.ξ 
                               }}
    ; F₁ = λ { {X} {Y} f → let module X = tab₀ X
                               module Y = tab₀ Y
                               module f = tab⇒ f
                               module α = NaturalTransformation α
                               pXX = p.F₀ (X.B , X.B)
                               pYY = p.F₀ (Y.B , Y.B)
                               qXY = q.F₀ (X.B , Y.B)
                               open SetoidR qXY in record 
      { arr = f.arr 
      ; eq = begin q.F₁ (id , f.arr) ⟨$⟩ (α.η (f.x.B , f.x.B) ⟨$⟩ f.x.ξ) ≈⟨ S.sym qXY (α.commute (id , f.arr) (S.refl pXX)) ⟩ 
                   α.η (f.x.B , f.y.B) ⟨$⟩ (p.F₁ (id , f.arr) ⟨$⟩ f.x.ξ) ≈⟨ cong (α.η (f.x.B , f.y.B)) f.eq ⟩ 
                   α.η (f.x.B , f.y.B) ⟨$⟩ (p.F₁ (f.arr , id) ⟨$⟩ f.y.ξ) ≈⟨ α.commute (f.arr , id) (S.refl pYY) ⟩ 
                   q.F₁ (f.arr , id) ⟨$⟩ (α.η (f.y.B , f.y.B) ⟨$⟩ f.y.ξ) ∎
      }}
    ; identity = λ { {A} → 
        let module A = tab₀ A 
            open SetoidR (q.F₀ (A.B , A.B)) in Equiv.refl }
    ; homomorphism = λ { {X} {Y} {Z} {f} {g} → 
        let module X = tab₀ X 
            module Y = tab₀ Y 
            module Z = tab₀ Z 
            module f = tab⇒ f 
            module g = tab⇒ g 
            open SetoidR (q.F₀ (f.x.B , g.x.B)) in Equiv.refl }
    ; F-resp-≈ = λ { {X} {Y} {f} {g} f≈g →   
        let module X = tab₀ X 
            module Y = tab₀ Y 
            module f = tab⇒ f 
            module g = tab⇒ g in f≈g }
    } 

open import Categories.Category.Construction.Functors using (Functors)
open import Categories.Category.Instance.Cats using (Cats)
open import Categories.NaturalTransformation.NaturalIsomorphism
  using (_≃_; niHelper)
  
𝕋ab : Functor (Functors (Product (Category.op C) C) (Setoids (o ⊔ ℓ ⊔ e) (o ⊔ ℓ ⊔ e))) (Cats (o ⊔ ℓ ⊔ e) (o ⊔ ℓ ⊔ e) e)
𝕋ab = record
  { F₀ = λ x → Tabulator x
  ; F₁ = λ α → h α
  ; identity = λ { {p} → niHelper (record 
       { η = λ { (X ∣ ξ) → 
           let module Pp = Functor p
               module Tp = Category (Tabulator p)
               pXX = Pp.F₀ (X , X)
               module R = SetoidR pXX
               open R
           in record { arr = id 
                     ; eq = begin _ ≈⟨ Pp.identity (S.refl pXX) ⟩ 
                                  _ ≈⟨ S.refl pXX ⟩ 
                                  _ ≈⟨ S.sym pXX (Pp.identity (S.refl pXX)) ⟩ 
                                  _ ∎ } } 
       ; η⁻¹ = λ { (X ∣ ξ) → 
           let module Pp = Functor p
               module Tp = Category (Tabulator p)
               pXX = Pp.F₀ (X , X)
               module R = SetoidR pXX
               open R
           in record { arr = id 
                     ; eq = begin _ ≈⟨ Pp.identity (S.refl pXX) ⟩ 
                                  _ ≈⟨ S.refl pXX ⟩ 
                                  _ ≈⟨ S.sym pXX (Pp.identity (S.refl pXX)) ⟩ 
                                  _ ∎ } } 
       ; commute = λ { {X ∣ ξ} {Y ∣ η} (arr ∥ eq) → 
           let module Pp = Functor p
               module Tp = Category (Tabulator p)
               open Tp using (Obj; _⇒_; _≈_; id; _∘_; module Equiv; module HomReasoning)
               open Tp.HomReasoning
               pXY = Pp.F₀ (X , Y)
           in begin _ ≈⟨ identityˡ ⟩ 
                    _ ≈⟨ Tp.Equiv.sym identityʳ ⟩ 
                    _ ∎ }
       ; iso = λ X → record { isoˡ = identityˡ ; isoʳ = identity² } 
       } ) }
  ; homomorphism = niHelper (record 
     { η = {!  !} 
     ; η⁻¹ = {!  !} 
     ; commute = {!  !} 
     ; iso = {!  !} 
     })
  ; F-resp-≈ = λ x → niHelper (record 
     { η = {!  !} 
     ; η⁻¹ = {!  !} 
     ; commute = {!  !} 
     ; iso = {!  !} 
     })
  }
