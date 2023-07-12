import Syntax.Simple.Signature as S
import Syntax.Typed.Signature  as T

module Syntax.Typed.Raw {SD : S.SigD} (D : T.SigD SD) where

module R where
  open import Syntax.Typed.Raw.Functor SD public
  open import Syntax.Typed.Raw.Term     D public
open R using (Raw; `_; _∋_; op) public
