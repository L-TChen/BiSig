open import Prelude

import Syntax.Simple.Description  as S
import Syntax.BiTyped.Description as B

module Syntax.BiTyped.RawNoMode.Term {SD : S.Desc} (Id : Set) (D : B.Desc {SD}) where

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
  op  : ⟦ D ⟧ Raw m              → Raw m

-- mutual
--   twkʳ : Raw m → Raw (n + m)
--   twkʳ (` x)   = ` x
--   twkʳ (t ⦂ A) = twkʳ t ⦂ wkʳ A 
--   twkʳ (op (D , i , ts)) = op (D , i , twkʳⁿ ts)
-- 
--   twkʳⁿ : {D : B.ArgsD Ξ}
--     → (⟦ D ⟧ᵃˢ Raw m) → (⟦ D ⟧ᵃˢ Raw (n + m))
--   twkʳⁿ {D = ∅}     (lift _) = _
--   twkʳⁿ {D = A ∙ D} (t , ts) = twkʳᵃ t , twkʳⁿ ts
-- 
--   twkʳᵃ : {D : List (TExp Ξ)}
--     → (⟦ D ⟧ᵃ Raw m) → (⟦ D ⟧ᵃ Raw (n + m))
--   twkʳᵃ {D = ∅}     t       = twkʳ t
--   twkʳᵃ {D = A ∙ D} (x , t) = x , twkʳᵃ t
