-- All the important Agda files with mappings to the paper

-- Checked with Agda 2.6.4.1
-- and Standard Library version 2.0 (included under agda-stdlib/)

-- The HTML version of this file (with hyperlinks to the imported files)
-- can be found at docs/README.html

{-# OPTIONS --safe --with-K #-}
-- The two options are also turned on globally in BiSig.agda-lib.

-- Section 2

import Example.Outline

-- Section 3

import Syntax.Simple.Signature     -- Definition 3.1
import Syntax.Simple.Term          -- Definition 3.1
import Syntax.Simple.Properties    -- Definition 3.3

import Syntax.Typed.Signature      -- Definitions 3.4 & 3.6
import Syntax.Typed.Raw.Functor
import Syntax.Typed.Raw.Term       -- Figure 5 (Definition 3.7)
import Syntax.Context              -- Definition 3.8
import Syntax.Typed.Term           -- Figure 6 (Definitions 3.9)
import Syntax.Typed.Functor

import Syntax.BiTyped.Signature    -- Definition 3.11 & 3.13
import Syntax.BiTyped.Functor
import Syntax.BiTyped.Term         -- Figure 7 (Definition 3.14)
import Syntax.BiTyped.Pre.Functor
import Syntax.BiTyped.Pre.Term     -- Figure 8 (Definition 3.14)
import Theory.Erasure              -- (Mode) erasure (after Definition 3.14)

import Example.STLC                -- Example 3.15, Appendix A

-- Section 4

import Theory.Soundness                -- Theorem 4.1 (the `if' part)
import Theory.Pre.TypingErasure
import Theory.Completeness             -- Theorem 4.1 (the `only if' part)

import Syntax.BiTyped.Pre.Generalised.Functor
import Syntax.BiTyped.Pre.Generalised.Term  -- Figure 9
import Theory.Pre.Term                 -- Lemmas 4.2 & 4.3
import Theory.ModeDecoration           -- Theorem 4.4, Lemma 4.5, Corollary 4.6

import Syntax.Typed.Raw.Ordering.Functor
import Syntax.Typed.Raw.Ordering.Term  -- Figure 10
import Theory.Pre.Annotatability       -- Proposition 4.7

-- Section 5

import Theory.ModeCorrectness.Signature    -- Definitions 5.1, 5.2, 5.3
import Theory.ModeCorrectness.Decidability -- Lemma 5.5
import Theory.ModeCorrectness.UniqueSynthesised  -- Lemma 5.6

import Theory.ModeCorrectness.Properties
import Theory.ModeCorrectness.Synthesis    -- Theorem 5.7
import Syntax.Simple.Term                  -- Definition 5.9
import Syntax.Simple.Unif                  -- Lemma 5.10

import Theory.Trichotomy                   -- Corollary 5.11

-- Section 6

import Example.Spine
import Example.Computational

-- Additional Examples

import Example.PCF
