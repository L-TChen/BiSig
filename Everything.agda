{-# OPTIONS --safe --with-K #-}

import Prelude.Level
import Prelude.Equivalence
import Prelude.Logic
import Prelude.Category
import Prelude.Distinct
import Prelude.DecEq
import Prelude

import Syntax.Simple.Description
import Syntax.Simple.Term
import Syntax.Simple.Properties
import Syntax.Simple.Unif
import Syntax.Simple

import Syntax.Context

import Syntax.Typed.Description
import Syntax.Typed.Functor
import Syntax.Typed.Term

import Syntax.Typed.Raw.Functor
import Syntax.Typed.Raw.Term
import Syntax.Typed.Raw.Ordering.Functor
import Syntax.Typed.Raw.Ordering.Term

import Syntax.BiTyped.Description
import Syntax.BiTyped.Functor
import Syntax.BiTyped.Term

import Syntax.BiTyped.Pre.Functor
import Syntax.BiTyped.Pre.Term
import Syntax.BiTyped.Pre.Generalised.Functor
import Syntax.BiTyped.Pre.Generalised.Term

import Theory.Erasure

import Theory.Soundness
import Theory.Completeness
import Theory.ModePreprocessing
import Theory.Pre.Term
import Theory.Pre.Annotatability
import Theory.Pre.TypingErasure

import Theory.ModeCorrectness.Description
import Theory.ModeCorrectness.Functor
import Theory.ModeCorrectness.UniqueSynthesised
import Theory.ModeCorrectness.Properties
import Theory.ModeCorrectness.Synthesis

import Example.Outline
import Example.STLC
