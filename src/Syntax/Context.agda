{-# OPTIONS --safe #-} 

open import Prelude
open import Syntax.Simple.Description

module Syntax.Context (D : Desc) where

open import Syntax.Context.Base   public
open import Syntax.Simple.Term  D

Cxt : ℕ → Set
Cxt m = Context (Tm m)
