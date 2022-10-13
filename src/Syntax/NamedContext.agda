open import Prelude
open import Syntax.Simple.Description

module Syntax.NamedContext (D : Desc) (Id : Set) where

open import Syntax.NamedContext.Base Id public
open import Syntax.Simple.Term       D

Cxt : ℕ → Set
Cxt m = Context (Tm m)
