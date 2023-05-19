{-# OPTIONS --safe #-}

open import Prelude

import Syntax.Simple.Description  as S
import Syntax.BiTyped.Description as B

module Syntax.BiTyped.RawNoMode.Term {SD : S.Desc} (Id : Set) (D : B.Desc SD) where

open import Syntax.Simple.Term SD
  renaming (Tm to TExp)

open import Syntax.BiTyped.RawNoMode.Functor {SD} Id

private variable
  Ξ n m : ℕ
  mod : Mode

infix 4 _⦂_

-- m is for the number of holes in a program
data Raw (m : ℕ) : Fam₀ where
  `_  : (x : Id)                 → Raw m
  _⦂_ : (t : Raw m) (A : TExp m) → Raw m
  op  : ⟦ D ⟧ (Raw m)            → Raw m

--mutual
--  twkˡ : Raw m → Raw (m + n)
--  twkˡ (` x)   = ` x
--  twkˡ (t ⦂ A) = twkˡ t ⦂ wkˡ A
--  twkˡ (op (i , ts)) = op (i , twkˡⁿ ts)
--
--  twkˡⁿ : {D : B.ArgsD Ξ}
--    → (⟦ D ⟧ᵃˢ Raw m) → (⟦ D ⟧ᵃˢ Raw (m + n))
--  twkˡⁿ {D = ∅}     (lift _) = _
--  twkˡⁿ {D = A ∙ D} (t , ts) = twkˡᵃ t , twkˡⁿ ts
--
--  twkˡᵃ : {D : List (TExp Ξ)}
--    → (⟦ D ⟧ᵃ Raw m) → (⟦ D ⟧ᵃ Raw (m + n))
--  twkˡᵃ {D = ∅}     t       = twkˡ t
--  twkˡᵃ {D = A ∙ D} (x , t) = x , twkˡᵃ t
