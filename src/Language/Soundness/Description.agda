open import Prelude

import Syntax.Simple.Description as S

module Language.Soundness.Description {SD : S.Desc} where

open import Data.List.Membership.Propositional

import Syntax.Typed.Description   {SD} as T
import Syntax.BiTyped.Description {SD} as B

open import Language.Erasure.Description

_≅_ : B.ConD → T.ConD → Set
BD ≅ D = eraseᶜ BD ≡ D

Soundness : B.Desc → T.Desc → Set
Soundness BDs TDs = ∀ {D} → D ∈ BDs → eraseᶜ D ∈ TDs

