{-# OPTIONS --safe #-}

import Prelude

import Syntax.Simple.Description
import Syntax.Simple.Term
import Syntax.Simple.Properties

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
import Theory.Pre.Term
import Theory.Pre.Annotatability
import Theory.Pre.TypingErasure
import Theory.ModePreprocessing
import Theory.Completeness

import Example.Outline
import Example.STLC
