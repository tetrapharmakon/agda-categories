{-# OPTIONS --without-K --safe --warning=noUserWarning #-}

open import Level using (_⊔_; lift; lower; zero)

open import Categories.Category using (Category)
open import Categories.Functor.Bifunctor using (Bifunctor; appˡ; appʳ)
open import Categories.Functor.Bifunctor.Properties

module Categories.Functor.Profunctor.Tabulator {o ℓ e} {C : Category o ℓ e} where
open import Data.Product
open import Categories.Functor renaming (id to idF)
open import Categories.Category.Instance.Setoids
open import Relation.Binary.Bundles renaming (Setoid to S)
import Relation.Binary.Reasoning.Setoid as SetoidR
open import Function.Equality using (Π; _⟶_; _⟨$⟩_; cong) renaming (_∘_ to _∗_)
open import Categories.Category.Product using (Product;_⁂_)
open import Categories.NaturalTransformation renaming (id to idN)
open import Categories.Morphism.Reasoning.Core C using (id-comm-sym)

private
  module 𝒞 = Category C

open 𝒞

record tab₀ (p : Bifunctor (Category.op C) C (Setoids (o ⊔ ℓ ⊔ e) (o ⊔ ℓ ⊔ e))) : Set (o ⊔ ℓ ⊔ e)
  where
    constructor _∣_
    field
      Car : Obj × Obj
    L = proj₁ Car 
    R = proj₂ Car
    field
      ξ : S.Carrier (Functor.F₀ p (L , R))


record tab⇒ (p : Bifunctor (Category.op C) C (Setoids (o ⊔ ℓ ⊔ e) (o ⊔ ℓ ⊔ e))) (x y : tab₀ p) : Set (o ⊔ ℓ ⊔ e) where
  constructor _,_∥_
  module x = tab₀ x
  module y = tab₀ y
  module p = Functor p
  field
    l : x.L ⇒ y.L
    r : x.R ⇒ y.R
    eq : S._≈_ (p.F₀ (x.L , y.R)) (p.F₁ (id , r) ⟨$⟩ x.ξ) (p.F₁ (l , id) ⟨$⟩ y.ξ)

Tabulator : ∀ (p : Bifunctor (Category.op C) C (Setoids (o ⊔ ℓ ⊔ e) (o ⊔ ℓ ⊔ e)))
          → Category (o ⊔ ℓ ⊔ e) (o ⊔ ℓ ⊔ e) e
Tabulator p = record
  { Obj = tab₀ p
  ; _⇒_ = λ { s t → tab⇒ p s t }
  ; _≈_ = λ h k → tab⇒.l h ≈ tab⇒.l k × tab⇒.r h ≈ tab⇒.r k
  ; id = λ { {A} → 
    let module p = Functor p 
        module A = tab₀ A
        pLR = p.F₀ (A.L , A.R) in id , id ∥ S.refl pLR }
  ; _∘_ = λ { {A} {B} {C} t s → 
    let module t = tab⇒ t
        module s = tab⇒ s
        module A = tab₀ A
        module B = tab₀ B
        module C = tab₀ C
        module p = Functor p
        pAA = p.F₀ (A.L , A.R)
        pBB = p.F₀ (B.L , B.R)
        pCC = p.F₀ (C.L , C.R)
        pLR = p.F₀ (A.L , C.R)
        module pL {A} = Functor (appˡ p A)
        module pR {A} = Functor (appʳ p A)
        open SetoidR pLR
    in (t.l ∘ s.l) , (t.r ∘ s.r) ∥ 
       (begin p.F₁ (id , t.r ∘ s.r) ⟨$⟩ A.ξ                 ≈⟨ pL.homomorphism (S.refl pAA) ⟩ -- 
              p.F₁ (id , t.r) ⟨$⟩ (p.F₁ (id , s.r) ⟨$⟩ A.ξ) ≈⟨ cong (p.F₁ (id , t.r)) s.eq ⟩ 
              p.F₁ (id , t.r) ⟨$⟩ (p.F₁ (s.l , id) ⟨$⟩ B.ξ) ≈⟨ [ p ]-commute (S.refl pBB) ⟩ 
              p.F₁ (s.l , id) ⟨$⟩ (p.F₁ (id , t.r) ⟨$⟩ B.ξ) ≈⟨ cong (p.F₁ (s.l , id)) t.eq ⟩ 
              p.F₁ (s.l , id) ⟨$⟩ (p.F₁ (t.l , id) ⟨$⟩ C.ξ) ≈⟨ S.sym pLR (pR.homomorphism (S.refl pCC)) ⟩
              p.F₁ (t.l ∘ s.l , id) ⟨$⟩ C.ξ                 ∎) }
  ; assoc = assoc , assoc
  ; sym-assoc = sym-assoc , sym-assoc
  ; identityˡ = λ { {A} {B} {f} → identityˡ , identityˡ }
  ; identityʳ = λ { {A} {B} {f} → identityʳ , identityʳ }
  ; identity² = λ { {A} → identity² , identity² }
  ; equiv = record 
    { refl = Equiv.refl , Equiv.refl 
    ; sym = λ {(leq , req) → (Equiv.sym leq) , (Equiv.sym req) }
    ; trans = λ {(leq , req) (leq' , req') → (Equiv.trans leq leq') , (Equiv.trans req req') }
    }
  ; ∘-resp-≈ = λ { (pl , pr) (ql , qr) → (∘-resp-≈ pl ql) , (∘-resp-≈ pr qr) }
  }

module _ {p : Bifunctor (Category.op C) C (Setoids (o ⊔ ℓ ⊔ e) (o ⊔ ℓ ⊔ e))} where
  
  projection : Functor (Tabulator p) C
  projection = record
    { F₀ = λ {(Car ∣ ξ) → proj₁ Car}
    ; F₁ = λ {(l , r ∥ eq) → l}
    ; identity = Equiv.refl
    ; homomorphism = Equiv.refl
    ; F-resp-≈ = λ { (el , _) → el}
    }

  projection' : Functor (Tabulator p) C
  projection' = record
    { F₀ = λ {(Car ∣ ξ) → proj₂ Car}
    ; F₁ = λ {(l , r ∥ eq) → r}
    ; identity = Equiv.refl
    ; homomorphism = Equiv.refl
    ; F-resp-≈ = λ { (_ , er) → er}
    }
  

  open import Categories.Functor.Hom using (Hom[_][-,-])
  
  open import Categories.Functor.Construction.LiftSetoids using (LiftSetoids)

  cell : NaturalTransformation (LiftSetoids zero (o ⊔ ℓ) ∘F Hom[ Tabulator p ][-,-]) (p ∘F (Functor.op projection ⁂ projection'))
  cell = ntHelper (record 
    { η = λ {(X , Y) → 
      let module X = tab₀ X 
          module Y = tab₀ Y 
          module p = Functor p in record 
          { _⟨$⟩_ = λ {u → p.F₁ (id , tab⇒.r (lower u)) ⟨$⟩ X.ξ}
          ; cong = λ { {lift i₁} {lift j₁} i≈j → 
              p.F-resp-≈ (Equiv.refl , proj₂ (lower i≈j)) (S.refl (p.F₀ (X.L , X.R))) -- p.F-resp-≈ (Equiv.refl , cong {!  !} i≈j) (S.refl (p.F₀ (X.L , X.R)))
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
              Pyy  = p.F₀ (y.L , y.R)
              Pxx  = p.F₀ (x.L , x.R)
              Pxx' = p.F₀ (x.L , x'.R)
              Pyy' = p.F₀ (y.L , y'.R)
              pf₁f₁ = p.F₀ (f₁.x.L , f₁.x.R)
              open SetoidR Pyy'
          in begin p.F₁ (id , f₂.r ∘ t.r ∘ f₁.r) ⟨$⟩ f₁.x.ξ                         ≈⟨ p.F-resp-≈ (Equiv.refl , ∘-resp-≈ʳ (∘-resp-≈ˡ (proj₂ (lower h)))) (S.refl Pyy) ⟩ 
          p.F₁ (id , f₂.r ∘ t'.r ∘ f₁.r) ⟨$⟩ f₁.x.ξ                                 ≈⟨ pL.homomorphism (S.refl pf₁f₁) ⟩
          p.F₁ (id , f₂.r) ⟨$⟩ (p.F₁ (id , t'.r ∘ f₁.r) ⟨$⟩ f₁.x.ξ)                 ≈⟨ cong (p.F₁ (id , f₂.r)) (pL.homomorphism (S.refl pf₁f₁)) ⟩
          p.F₁ (id , f₂.r) ⟨$⟩ (p.F₁ (id , t'.r) ⟨$⟩ (p.F₁ (id , f₁.r) ⟨$⟩ f₁.x.ξ)) ≈⟨ cong (p.F₁ (id , f₂.r)) (cong (p.F₁ (id , t'.r)) f₁.eq) ⟩
          p.F₁ (id , f₂.r) ⟨$⟩ (p.F₁ (id , t'.r) ⟨$⟩ (p.F₁ (f₁.l , id) ⟨$⟩ x.ξ))    ≈⟨ cong (p.F₁ (id , f₂.r)) ([ p ]-commute (S.refl Pxx)) ⟩
          p.F₁ (id , f₂.r) ⟨$⟩ (p.F₁ (f₁.l , id) ⟨$⟩ (p.F₁ (id , t'.r) ⟨$⟩ x.ξ))    ≈˘⟨ [ p ]-decompose₂ (S.refl Pxx') ⟩
          p.F₁ (f₁.l , f₂.r) ⟨$⟩ (p.F₁ (id , t'.r) ⟨$⟩ x.ξ) ∎ }
    })

module _ {p q : Bifunctor (Category.op C) C (Setoids (o ⊔ ℓ ⊔ e) (o ⊔ ℓ ⊔ e))} where

  h : (α : NaturalTransformation p q) → Functor (Tabulator p) (Tabulator q)
  h α = let module p = Functor p 
            module q = Functor q 
            module α = NaturalTransformation α in record
    { F₀ = λ {(C ∣ ξ) → C ∣ (α.η C ⟨$⟩ ξ)}
    ; F₁ = λ { {X@(C ∣ ξ)} {Y@(D ∣ η)} f@(l , r ∥ eq) → 
        let module X = tab₀ X
            module Y = tab₀ Y
            module f = tab⇒ f
            pXX = p.F₀ (X.L , X.R)
            pYY = p.F₀ (Y.L , Y.R)
            qXY = q.F₀ (X.L , Y.R)
            open SetoidR qXY in 
            l , r ∥  (begin q.F₁ (id , r) ⟨$⟩ (α.η C ⟨$⟩ ξ) ≈˘⟨ α.commute (id , r) (S.refl pXX) ⟩
                            α.η (f.x.L , f.y.R) ⟨$⟩ (f.p.F₁ (id , r) ⟨$⟩ ξ) ≈⟨ cong (α.η (f.x.L , f.y.R)) f.eq ⟩
                            α.η (f.x.L , f.y.R) ⟨$⟩ (f.p.F₁ (l , id) ⟨$⟩ η) ≈⟨ α.commute (l , id) (S.refl pYY) ⟩
                            q.F₁ (l , id) ⟨$⟩ (α.η D ⟨$⟩ η) ∎) }
    ; identity = λ { {A} → Equiv.refl , Equiv.refl }
    ; homomorphism =  λ { {X} {Y} {Z} {f} {g} → Equiv.refl , Equiv.refl }
    ; F-resp-≈ = λ { {X} {Y} {f} {g} f≈g → f≈g }
    }


open import Categories.Category.Construction.Functors using (Functors)
open import Categories.Category.Instance.Cats using (Cats)
open import Categories.NaturalTransformation.NaturalIsomorphism
  using (niHelper)
  
𝕋ab : Functor (Functors (Product (Category.op C) C) (Setoids (o ⊔ ℓ ⊔ e) (o ⊔ ℓ ⊔ e))) (Cats (o ⊔ ℓ ⊔ e) (o ⊔ ℓ ⊔ e) e)
𝕋ab = record
  { F₀ = λ x → Tabulator x
  ; F₁ = λ α → h α
  ; identity = λ { {p} → niHelper (record 
    { η = λ {
      (X ∣ ξ) → 
        let module Pp = Functor p
            pLR = Pp.F₀ X
        in id , id ∥ S.refl pLR
      }
    ; η⁻¹ = λ {
      (X ∣ ξ) → 
        let module Pp = Functor p
            pLR = Pp.F₀ X
        in id , id ∥ S.refl pLR
      }
    ; commute = λ { {X ∣ ξ} {Y ∣ η} (l , r ∥ eq) → id-comm-sym , id-comm-sym  }
    ; iso = λ X → record { isoˡ = identityˡ , identityˡ ; isoʳ = identity² , identity² } 
    }) }
  ; homomorphism = λ { {p} {q} {r} {α} {β} → 
    let module Pr = Functor r in
    niHelper (record 
      { η = λ {
      (X ∣ ξ) → 
        let module Pp = Functor p
            pLR = Pp.F₀ X
            rLR = Pr.F₀ X
        in id , id ∥ cong (Pr.F₁ (id , id)) (S.refl rLR) }
      ; η⁻¹ = λ {
      (X ∣ ξ) → 
        let module Pp = Functor p
            pLR = Pp.F₀ X
            rLR = Pr.F₀ X
        in id , id ∥ cong (Pr.F₁ (id , id)) (S.refl rLR) }
      ; commute = λ { {X ∣ ξ} {Y ∣ η} (l , r ∥ eq) → id-comm-sym , id-comm-sym  }
      ; iso = λ X → record { isoˡ = identityˡ , identityˡ ; isoʳ = identity² , identity² } 
      }) }
  ; F-resp-≈ = λ { {p} {q} {α} {β} f≈g → 
    let module Pp = Functor p 
        module Pq = Functor q in niHelper (record 
        { η = λ { (X ∣ _) → let pLR = Pp.F₀ X in
              id , id ∥ cong (Pq.F₁ (id , id)) (f≈g (S.refl pLR)) }
        ; η⁻¹ = λ { (X ∣ _) → let pLR = Pp.F₀ X in
                id , id ∥ cong (Pq.F₁ (id , id)) (S.sym (Pq.F₀ X) (f≈g (S.refl pLR))) }
        ; commute = λ { {X ∣ ξ} {Y ∣ η} (l , r ∥ eq) → id-comm-sym , id-comm-sym  }
        ; iso = λ X → record { isoˡ = identityˡ , identityˡ ; isoʳ = identity² , identity² } 
        }) }
  }