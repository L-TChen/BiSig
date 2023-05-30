{-# OPTIONS --safe #-}

open import Prelude

import Syntax.Simple.Description as S

module Theory.Completeness.Description (SD : S.Desc) where

open import Syntax.Simple  SD
open import Syntax.Context SD

open import Syntax.Typed.Description    SD as T
open import Syntax.BiTyped.Description  SD as B

open import Theory.Erasure.Description

-- A bidirectional typing is complete w.r.t. a base typing if every typing rule in the base typing
-- has a corresponding typing rule.
Completeness : B.Desc → T.Desc → Set
Completeness BD TD = (i : TD .Op) → Σ[ j ∈ BD .Op ] eraseᶜ (BD .rules j) ≡ TD .rules i
