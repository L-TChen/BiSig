{-# OPTIONS --rewriting #-}

import Prelude

import Syntax.Context
import Syntax.NamedContext

-- Syntaxes
import Syntax.Simple.Description
import Syntax.Simple.Term
import Syntax.Simple.Association
import Syntax.Simple.Properties
import Syntax.Simple.Unification
import Syntax.Simple.Unification.Properties

import Syntax.Typed.Description
import Syntax.Typed.Intrinsic.Functor
import Syntax.Typed.Intrinsic.Term
import Syntax.Typed.Intrinsic.Operation
import Syntax.Typed.Intrinsic.Properties

import Syntax.BiTyped.Description
import Syntax.BiTyped.Intrinsic.Functor
import Syntax.BiTyped.Intrinsic.Term
import Syntax.BiTyped.Raw.Functor
import Syntax.BiTyped.Raw.Term
import Syntax.BiTyped.RawNoMode.Functor
import Syntax.BiTyped.RawNoMode.Term
import Syntax.BiTyped.Extrinsic.Functor
import Syntax.BiTyped.Extrinsic.Term
import Syntax.BiTyped.Extrinsic.Properties

-- [TODO] Type-level specifications should make it clear that we’re operating on the same syntax tree throughout.
--        For example: scope checking, bidirectionalisation of raw terms, conversion between extrinsic and intrinsic terms
-- [TODO] What format (intrinsic vs extrinsic) does the compiler need eventually?
-- [TODO] User interface (for extending existing systems): correct and convenient bidirectional annotation of a base type system
-- [TODO] history of parser generators

-- Theory of Bidirectional Type Checking
import Theory.Annotatability.Description
import Theory.Annotatability.Term

import Theory.RawAnnotatability  -- [TODO] metavariables needed for converting to bidirectional raw syntax
import Theory.Soundness

import Theory.Erasure.Description
import Theory.Erasure.Term

import Theory.Ontologisation.Context
import Theory.Ontologisation.Term

import Theory.ModeCorrectness.Description
-- import Theory.ModeCorrectness.Term -- [TODO] not finished yet
                                   -- [TODO] migrate to de Bruijn–indexed raw terms

-- Examples

import Example.Implicational
import Example.STLC
import Example.BiSTLC
