-- All the important Agda files with mappings to the paper

-- Checked with Agda 2.6.3
-- and Standard Library version 7c5f3ff9 (included under agda-stdlib/)

-- The HTML version of this file (with hyperlinks to the imported files)
-- can be found at html/README.html.

{-# OPTIONS --safe --with-K #-}
-- The two options are also turned on globally in BiSig.agda-lib.

-- Section 2

import Example.Outline

-- Section 3

import Syntax.Simple.Description   -- Definition 3.1
import Syntax.Simple.Term          -- Figure 5 (Definition 3.1)
import Syntax.Simple.Properties    -- Definition 3.3

import Syntax.Typed.Description    -- Definitions 3.4 & 3.6
import Syntax.Typed.Raw.Term       -- Figure 6 (Definition 3.7)
import Syntax.Typed.Raw.Functor
import Syntax.Context              -- Definition 3.8
import Syntax.Typed.Term           -- Figure 7 (Definitions 3.9)
import Syntax.Typed.Functor


import Syntax.BiTyped.Description  -- Definition 3.11 & 3.13
import Theory.Erasure              -- (Mode) erasure
import Syntax.BiTyped.Term         -- Figure 8 (Definition 3.14)
import Syntax.BiTyped.Functor
import Syntax.BiTyped.Pre.Term     -- Figure 9 (Definition 3.14)
import Syntax.BiTyped.Pre.Functor

import Example.STLC                -- STLC examples

-- Section 4

import Theory.Soundness                -- Theorem 4.1
import Theory.Pre.TypingErasure
import Theory.Completeness

import Syntax.BiTyped.Pre.Generalised.Term  -- Figure 10
import Syntax.BiTyped.Pre.Generalised.Functor
import Theory.Pre.Term                 -- Lemmas 4.2 & 4.3
import Theory.ModePreprocessing        -- Theorem 4.4, Lemma 4.5, Corollary 4.6

import Syntax.Typed.Raw.Ordering.Term  -- Figure 11
import Syntax.Typed.Raw.Ordering.Functor
import Theory.Pre.Annotatability       -- Proposition 4.7

-- Section 5

import Theory.ModeCorrectness.Description  -- Definitions 5.1 & 5.3
import Theory.ModeCorrectness.Functor      -- Definition 5.2
import Theory.ModeCorrectness.UniqueSynthesised  -- Lemma 5.5

import Theory.ModeCorrectness.Synthesis    -- Theorem 5.6
import Theory.ModeCorrectness.Properties
import Syntax.Simple.Term                  -- Definition 5.8
import Syntax.Simple.Unif                  -- Lemma 5.9

import Theory.Trichotomy                   -- Corollary 5.10
