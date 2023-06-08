open import Prelude
import Syntax.Simple.Description as S
import Syntax.Typed.Description  as T

module Syntax.Typed.Intrinsic.Properties {SD : S.Desc} {D : T.Desc SD} where
open import Syntax.Simple SD

open import Syntax.Context SD

open import Syntax.Typed.Intrinsic.Functor
open import Syntax.Typed.Intrinsic.Term D
