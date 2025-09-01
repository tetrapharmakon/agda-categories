import Level

open import Categories.Category.Core
open import Categories.Functor

module NotFun {o l e} {C : Category o l e} where

_ : Functor C (Category.op C)
_ = record 
  { F₀ = λ { x → x } 
  ; F₁ = λ { f → {! op !} } 
  ; identity = {! !} 
  ; homomorphism = {! !} 
  ; F-resp-≈ = {! !} 
  }
