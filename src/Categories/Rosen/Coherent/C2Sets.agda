{-# OPTIONS --without-K --warning=noUserWarning --warning=noUselessPrivate --warning=noUnsupportedIndexedMatch #-}

-- The category of C₂-sets (sets equipped with an action of the cyclic
-- group of order 2), and the concrete counterexample it witnesses to the
-- reverse direction of `Categories.Rosen.Coherent.NaturalAndHom.lem`
-- (see the comment above `false` there): the nontrivial central element
-- of C₂ acts as a natural endomorphism of the identity functor that is
-- the identity on the terminal object but swaps the regular C₂-set, so
-- `p` (component-at-the-unit) loses information that `ι` cannot
-- reconstruct.
--
-- C₂-sets is exhibited as Cartesian closed (in the canonical style:
-- explicit product/exponential operations, mirroring how
-- Categories.Rosen.Cartesian.Sets exhibits Sets as a CCC), and its
-- Monoidal/Closed structure is *deduced* from that via
-- CartesianMonoidal/CartesianMonoidalClosed, exactly as Sets-Monoidal and
-- Sets-Closed are deduced there. The canonical product and internal hom
-- are built concretely (pointwise, with the internal hom's C₂-action
-- given by conjugation), and all of the accompanying coherence proofs
-- (naturality, functoriality, the CartesianClosed laws) are proved too.
-- The swap natural transformation itself is also constructed: its
-- naturality is definitional, since being a morphism of C₂-sets already
-- means commuting with the action of every element of C₂ (in particular
-- the nontrivial one). `swap-is-counterexample` -- the actual
-- impossibility proof -- is proved too, via a small chain of lemmas
-- (see the comments above each one); the only thing left open is
-- `ι-id≈actBy-false`, an interesting fact in its own right that the
-- final proof turned out not to need.

module Categories.Rosen.Coherent.C2Sets where

open import Data.Bool using (Bool; false; true; T; _xor_)
open import Data.Bool.Properties using (xor-assoc; xor-comm; xor-identityˡ; xor-identityʳ; xor-same)
open import Data.Empty using (⊥)
import Data.Unit as Unit
open import Data.Product using (_,_) renaming (_×_ to _×′_)
open import Data.Unit.Polymorphic using (⊤; tt)
open import Level using (Level; 0ℓ; Lift; lift; lower)
open import Relation.Binary.PropositionalEquality using (_≡_; cong; cong₂; subst; sym; trans)
import Relation.Binary.PropositionalEquality as ≡

open import Categories.Category using (Category)
open import Categories.Category.Cartesian.Monoidal using (module CartesianMonoidal)
open import Categories.Category.CartesianClosed as CCC
open import Categories.Category.CartesianClosed.Canonical as Canonical
open import Categories.Category.Construction.Functors using (Functors)
open import Categories.Category.Instance.Sets using (Sets)
open import Categories.Category.Monoidal using (Monoidal)
open import Categories.Category.Monoidal.Closed using (Closed)
open import Categories.Functor using (Functor) renaming (id to idF)
open import Categories.NaturalTransformation using (NaturalTransformation; ntHelper)
open import Categories.Rosen.Cartesian.Sets using (extensionality)
open import Relation.Nullary using (¬_)

-- C₂ as a one-object category: the single object's endomorphisms are the
-- two group elements, composed via xor (so `false` is the identity `e`
-- and `true` is the nontrivial element `g`, with `g ∘ g ≈ e`).
C2 : Category 0ℓ 0ℓ 0ℓ
C2 = record
  { Obj       = ⊤
  ; _⇒_       = λ _ _ → Bool
  ; _≈_       = _≡_
  ; id        = false
  ; _∘_       = _xor_
  ; assoc     = λ {_} {_} {_} {_} {f} {g} {h} → xor-assoc h g f
  ; sym-assoc = λ {_} {_} {_} {_} {f} {g} {h} → sym (xor-assoc h g f)
  ; identityˡ = λ {_} {_} {f} → xor-identityˡ f
  ; identityʳ = λ {_} {_} {f} → xor-identityʳ f
  ; identity² = xor-identityˡ false
  ; equiv     = ≡.isEquivalence
  ; ∘-resp-≈  = cong₂ _xor_
  }

module _ (o : Level) where

  -- C₂-sets, as the presheaf category on C₂ -- i.e. functors C2 → Sets o,
  -- with natural transformations as morphisms. All category laws come
  -- for free from the generic Functors construction.
  C2Sets : Category _ _ _
  C2Sets = Functors C2 (Sets o)

  -- The canonical (pointwise) product of two C₂-sets, with the diagonal
  -- action: (P × Q) carries the C₂-action b · (x , y) = (b · x , b · y).
  _C×_ : Functor C2 (Sets o) → Functor C2 (Sets o) → Functor C2 (Sets o)
  P C× Q = record
    { F₀ = λ _ → P.F₀ tt ×′ Q.F₀ tt
    ; F₁ = λ b (x , y) → P.F₁ b x , Q.F₁ b y
    ; identity = λ { {x = (a , b)} → cong₂ _,_ P.identity Q.identity }
    ; homomorphism = λ { {f = f} {g = g} {x = (a , b)} → cong₂ _,_ P.homomorphism Q.homomorphism }
    ; F-resp-≈ = λ { eq {x = (a , b)} → cong₂ _,_ (P.F-resp-≈ eq) (Q.F-resp-≈ eq) }
    }
    where module P = Functor P
          module Q = Functor Q

  -- The canonical terminal C₂-set: the one-point set, with the (unique,
  -- trivial) action.
  C⊤ : Functor C2 (Sets o)
  C⊤ = record
    { F₀ = λ _ → ⊤
    ; F₁ = λ _ _ → tt
    ; identity = ≡.refl
    ; homomorphism = ≡.refl
    ; F-resp-≈ = λ _ → ≡.refl
    }

  C! : ∀ {P} → NaturalTransformation P C⊤
  C! = ntHelper record { η = λ _ _ → tt ; commute = λ _ → λ {x} → ≡.refl }

  Cπ₁ : ∀ {P Q} → NaturalTransformation (P C× Q) P
  Cπ₁ = ntHelper record { η = λ _ (x , _) → x ; commute = λ _ → λ {x} → ≡.refl }

  Cπ₂ : ∀ {P Q} → NaturalTransformation (P C× Q) Q
  Cπ₂ = ntHelper record { η = λ _ (_ , y) → y ; commute = λ _ → λ {y} → ≡.refl }

  C⟨_,_⟩ : ∀ {P Q R} → NaturalTransformation R P → NaturalTransformation R Q → NaturalTransformation R (P C× Q)
  C⟨_,_⟩ f g = ntHelper record
    { η = λ X x → f.η X x , g.η X x
    ; commute = λ h → cong₂ _,_ (f.commute h) (g.commute h)
    }
    where module f = NaturalTransformation f 
          module g = NaturalTransformation g

  -- Every element of C₂ is self-inverse (b ∘ b ≈ e), so every C₂-set's
  -- action is an involution -- this is exactly what makes the
  -- conjugation action on the internal hom well behaved.
  involutive : ∀ {R : Functor C2 (Sets o)} (b : Bool) {x} →
               Functor.F₁ R b (Functor.F₁ R b x) ≡ x
  involutive {R} b {x} = trans (sym R.homomorphism) (trans (cong (λ e → R.F₁ e x) (xor-same b)) R.identity)
    where module R = Functor R

  -- The canonical internal hom of two C₂-sets: the function space, with
  -- the conjugation action b · h = λ x → b · h (b · x) (well defined
  -- since every element of C₂ is self-inverse).
  _C^_ : Functor C2 (Sets o) → Functor C2 (Sets o) → Functor C2 (Sets o)
  Q C^ P = record
    { F₀ = λ _ → P.F₀ tt → Q.F₀ tt
    ; F₁ = λ b h x → Q.F₁ b (h (P.F₁ b x))
    ; identity = λ { {x = h} → extensionality (λ y →
        trans (cong (λ z → Q.F₁ false (h z)) P.identity) Q.identity) }
    ; homomorphism = λ { {f = f} {g = g} {x = h} → extensionality (λ y →
        trans (cong (λ z → Q.F₁ (g xor f) z)
                     (cong h (trans (cong (λ b → P.F₁ b y) (xor-comm g f)) (P.homomorphism {f = g} {g = f}))))
              (Q.homomorphism {f = f} {g = g})) }
    ; F-resp-≈ = λ { eq {x = h} → extensionality (λ y → cong (λ b → Q.F₁ b (h (P.F₁ b y))) eq) }
    }
    where module P = Functor P
          module Q = Functor Q

  Ceval : ∀ {P Q} → NaturalTransformation ((Q C^ P) C× P) Q
  Ceval {P} {Q} = ntHelper record
    { η = λ _ (k , x) → k x
    ; commute = λ { b {x = (k , x)} → cong (Q.F₁ b) (cong k (involutive {P} b)) }
    }
    where module Q = Functor Q

  Ccurry : ∀ {P Q R} → NaturalTransformation (R C× P) Q → NaturalTransformation R (Q C^ P)
  Ccurry {P} {R = R} f = ntHelper record
    { η = λ X c x → f.η X (c , x)
    ; commute = λ { h {x = c} → extensionality (λ x →
        trans (sym (cong (λ z → f.η _ (R.F₁ h c , z)) (involutive {P} h))) (f.commute h {x = c , P.F₁ h x})) }
    }
    where module f = NaturalTransformation f
          module P = Functor P
          module R = Functor R

  -- C₂-sets is Cartesian closed, in the canonical style, built from the
  -- concrete product/exponential data above (_C×_, C⊤, Cπ₁, Cπ₂, C⟨_,_⟩,
  -- _C^_, Ceval, Ccurry).
  C2Sets-Canonical : Canonical.CartesianClosed C2Sets
  C2Sets-Canonical = record
    { ⊤ = C⊤
    ; _×_ = _C×_
    ; ! = C!
    ; π₁ = Cπ₁
    ; π₂ = Cπ₂
    ; ⟨_,_⟩ = C⟨_,_⟩
    ; !-unique = λ f → ≡.refl
    ; π₁-comp = ≡.refl
    ; π₂-comp = ≡.refl
    ; ⟨,⟩-unique = λ p q → cong₂ _,_ (sym p) (sym q)
    ; _^_ = _C^_
    ; eval = Ceval
    ; curry = Ccurry
    ; eval-comp = ≡.refl
    ; curry-resp-≈ = λ { eq {_} {c} → extensionality (λ y → eq {_} {c , y}) }
    ; curry-unique = λ { eq {_} {c} → extensionality (λ y → eq {_} {c , y}) }
    }

  C2Sets-CCC : CCC.CartesianClosed C2Sets
  C2Sets-CCC = Canonical.Equivalence.fromCanonical _ C2Sets-Canonical

  module C2Sets-MonoidalClosed where
    private
      module CMC = CCC.CartesianMonoidalClosed C2Sets C2Sets-CCC
      open CMC using (closedMonoidal)
      open CartesianMonoidal (CCC.CartesianClosed.cartesian C2Sets-CCC) using (monoidal)

    -- Deduced from C2Sets-CCC, exactly as Sets-Monoidal is from Sets-CCC.
    C2Sets-Monoidal : Monoidal C2Sets
    C2Sets-Monoidal = monoidal

    C2Sets-Closed : Closed C2Sets-Monoidal
    C2Sets-Closed = closedMonoidal

  open C2Sets-MonoidalClosed using (C2Sets-Monoidal; C2Sets-Closed)

  open Closed C2Sets-Closed using ([_,-]; unit)
  open Category C2Sets using (_≈_; _⇒_; id; module Equiv)
  open import Categories.Rosen.Coherent.NaturalAndHom C2Sets-Closed using (p; ι)

  -- "Act by b": the natural endomorphism of the identity functor on
  -- C₂-sets sending x to b · x (via the constant-embedding identification
  -- of X with [unit,X]). swap is the b = true instance -- the nontrivial
  -- central element of C₂ -- but the construction and its naturality
  -- proof don't care which b we pick, since C₂ is abelian: any fixed
  -- group element acts naturally on the identity functor of its category
  -- of sets, by the same argument as before with `true` replaced by `b`.
  actBy : Bool → NaturalTransformation idF ([_,-] unit)
  actBy b = ntHelper (record
    { η = λ X → let module X = Functor X in ntHelper (record
      { η = λ tt s t → X.F₁ b s
      ; commute = λ { f {x = s} → cong (λ e _ → e)
          (trans (sym (X.homomorphism {f = f} {g = b}))
                 (trans (cong (λ e → X.F₁ e s) (xor-comm b f))
                        (X.homomorphism {f = b} {g = f}))) }
      })
    ; commute = λ { f {_} {s} → cong (λ e _ → e) (sym (NaturalTransformation.commute f b)) }
    })

  -- The nontrivial central element of C₂, acting as a natural
  -- endomorphism of the identity functor on C₂-sets: the identity on the
  -- terminal object, but the swap map on the regular C₂-set.
  swap : NaturalTransformation idF ([_,-] unit)
  swap = actBy true

  -- The regular representation: C₂ acting on itself by translation. This
  -- is the witness that distinguishes swap from the identity: the action
  -- of the nontrivial element has no fixed points here.
  Creg : Functor C2 (Sets o)
  Creg = record
    { F₀ = λ _ → Lift o Bool
    ; F₁ = λ b (lift x) → lift (b xor x)
    ; identity = λ { {x = lift x} → cong lift (xor-identityˡ x) }
    ; homomorphism = λ { {f = f} {g = g} {x = lift x} → cong lift (xor-assoc g f x) }
    ; F-resp-≈ = λ { eq {x = lift x} → cong lift (cong (_xor x) eq) }
    }

  -- Step 1: p swap ≈ id, because Hom(unit,unit) is a singleton (unit is
  -- terminal), so *any* two morphisms unit ⇒ unit -- in particular
  -- `p swap` and `id` -- are ≈.
  p-swap≈id : p {A = unit} swap ≈ id
  p-swap≈id = ≡.refl

  -- Step 2: ι respects ≈ (a general fact about ι, provable from the
  -- [-,-] bifunctor's F-resp-≈, independent of what ξ, ξ' actually are).
  ι-resp-≈ : ∀ {ξ ξ' : unit ⇒ unit} → ξ ≈ ξ' → ∀ X →
             NaturalTransformation.η (ι {A = unit} ξ) X ≈ NaturalTransformation.η (ι {A = unit} ξ') X
  ι-resp-≈ = λ z X {x} {x = x₁} → ≡.refl

  -- Step 3 (not needed below, see the note on `collapse`): ι id agrees
  -- with actBy false -- i.e. with the *actually trivial* action -- at
  -- every object X. Unlike the other steps this does NOT close by refl:
  -- unfolding [unit,-].F₀ X reveals it's built via
  -- Categories.Functor.Construction.Constant rather than reducing
  -- straight to the "constant embedding" `⊤ → X.F₀ tt` I assumed by
  -- analogy with actBy's own construction, so this would need actually
  -- tracing through that (and the surrounding adjunction machinery) to
  -- prove for a generic X. Left open as an interesting fact in its own
  -- right, orthogonal to swap-is-counterexample below.
  ι-id≈actBy-false : ∀ X →
                      NaturalTransformation.η (ι {A = unit} id) X ≈ NaturalTransformation.η (actBy false) X
  ι-id≈actBy-false = λ X → {! !}

  -- Steps 1-3 combined at Creg: η(ι(p swap)) Creg ≈ η(actBy false) Creg.
  -- Closes by refl directly -- Creg's action computes by xor, which
  -- unfolds far enough that Agda can see the equation hold without
  -- needing ι-id≈actBy-false (or even p-swap≈id / ι-resp-≈) as a
  -- separate step; it was really only needed as a proof *plan*.
  collapse : NaturalTransformation.η (ι {A = unit} (p {A = unit} swap)) Creg ≈ NaturalTransformation.η (actBy false) Creg
  collapse = ≡.refl

  -- The concrete instance of the fact from the comment in NaturalAndHom:
  -- p loses information about swap that ι cannot reconstruct, so the
  -- reverse direction of `lem` genuinely fails for C₂-sets.
  swap-is-counterexample :
    ¬ (∀ X → NaturalTransformation.η (ι {A = unit} (p {A = unit} swap)) X ≈ NaturalTransformation.η swap X)
  swap-is-counterexample H = subst T final-eq Unit.tt
    where
    -- η swap Creg ≈ η(actBy false) Creg, i.e. sym (H Creg) ○ collapse,
    -- with the implicit C₂-object/point arguments bound explicitly:
    -- composing them via the generic Equiv.trans (rather than plain
    -- `trans` after binding down to the point-level equation) hits the
    -- same higher-order-unification wall as before, since H is itself
    -- an opaque bound variable.
    swap≈actBy-false : NaturalTransformation.η swap Creg ≈ NaturalTransformation.η (actBy false) Creg
    swap≈actBy-false {_} {s} = trans (sym (H Creg {_} {s})) (collapse {_} {s})

    -- Evaluate both sides at the point `lift false`, and at the dummy
    -- unit-argument `tt`: true ≡ false. This part is genuine, mechanical
    -- glue -- it only needs swap≈actBy-false's *type*, not its proof.
    final-eq : true ≡ false
    final-eq = cong lower (cong (λ h → h tt) (swap≈actBy-false {_} {lift false}))
