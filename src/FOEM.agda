open import Categories.Category.Core

import Level

open import Categories.Monad

module FOEM {o o' l l' e e'} {params : Category o l e} {carriers : Category o' l' e'} {T : params → Monads carriers} where