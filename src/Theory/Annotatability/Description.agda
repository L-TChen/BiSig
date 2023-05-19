{-# OPTIONS --safe #-}

open import Prelude

import Syntax.Simple.Description as S

module Theory.Annotatability.Description (SD : S.Desc) where

open import Syntax.Simple.Term SD
  renaming (Tm to TExp; Tms to TExps; Sub to TSub)
open import Syntax.Context SD

open import Syntax.Typed.Description    SD as T
open import Syntax.BiTyped.Description  SD as B

open import Theory.Erasure.Description

-- A bidirectional typing annotates a base typing if every typing rule in the base typing
-- has a corresponding typing rule.
Annotatability : B.Desc → T.Desc → Set
Annotatability BD TD = (i : TD .Op) → Σ[ j ∈ BD .Op ] eraseᶜ (BD .rules j) ≡ TD .rules i
