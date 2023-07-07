{-# OPTIONS --safe --with-K #-}
-- Syntaxes
import Syntax.Simple.Description
import Syntax.Simple.Term
import Syntax.Simple.Properties
import Syntax.Simple.Unif
import Syntax.Simple

import Syntax.Typed.Description
import Syntax.Typed.Intrinsic.Functor
import Syntax.Typed.Intrinsic.Term
import Syntax.Typed.Intrinsic.Operation
import Syntax.Typed.Intrinsic.Properties
import Syntax.Typed.Raw.Functor
import Syntax.Typed.Raw.Term
import Syntax.Typed.Extrinsic.Functor
import Syntax.Typed.Extrinsic.Term

import Syntax.BiTyped.Description
import Syntax.BiTyped.Intrinsic.Functor
import Syntax.BiTyped.Intrinsic.Term
import Syntax.BiTyped.Raw.Functor
import Syntax.BiTyped.Raw.Term
import Syntax.BiTyped.Extrinsic.Functor
import Syntax.BiTyped.Extrinsic.Term
import Syntax.BiTyped.Extrinsic.Properties

-- [TODO] User interface (for extending existing systems): correct and convenient bidirectional annotation of a base type system
import Theory.Soundness

import Theory.Completeness.Description
import Theory.Completeness.Term

import Theory.Erasure.Description
import Theory.Erasure.Term

import Theory.Ontologisation.Context
import Theory.Ontologisation.Term

import Theory.ModeCorrectness.Description
import Theory.ModeCorrectness.Functor
import Theory.ModeCorrectness.UniqueSynthesised
import Theory.ModeCorrectness.Properties
import Theory.ModeCorrectness.Synthesis 

-- Examples

import Example.Implicational
import Example.STLC
import Example.BiSTLC
import Example.Outline