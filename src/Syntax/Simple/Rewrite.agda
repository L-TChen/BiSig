{-# OPTIONS --with-K --rewriting  #-}

open import Syntax.Simple.Description

module Syntax.Simple.Rewrite (D : Desc) where

open import Prelude

open import Syntax.Simple.Term       D
open import Syntax.Simple.Properties D
open import Syntax.Simple.Association D

open import Agda.Builtin.Equality.Rewrite

private variable
  n m l : ℕ
  A   : Set
  t u : Tm n
  σ ρ : AList m n

lem1 : (σ : AList m n) (ρ : AList n l) → toSub (σ ⨟ ρ) ≡ toSub σ ⨟ toSub ρ
lem1 σ ρ = toSub-++ σ ρ

lem2 : (i : Fin n) → lookup (tabulate `_) i ≡ ` i
lem2 = lookup∘tabulate `_

{-# REWRITE lem1 lem2 #-}
