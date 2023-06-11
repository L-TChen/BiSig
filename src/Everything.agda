{-# OPTIONS --safe #-}

import Prelude

import Syntax.Context

-- Syntaxes
import Syntax.Simple.Description
import Syntax.Simple.Term
import Syntax.Simple.Association
import Syntax.Simple.Properties
import Syntax.Simple.Unification
import Syntax.Simple.Unification.Properties

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
import Theory.Pre.Term
import Theory.Pre.Annotatability
import Theory.Bidirectionalisation
import Theory.Completeness

-- Examples

import Example.Implicational
import Example.STLC
import Example.BiSTLC
import Example.Outline
