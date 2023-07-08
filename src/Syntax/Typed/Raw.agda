import Syntax.Simple.Description as S
import Syntax.Typed.Description  as T

module Syntax.Typed.Raw {SD : S.Desc} (D : T.Desc SD) where

module R where
  open import Syntax.Typed.Raw.Functor SD public
  open import Syntax.Typed.Raw.Term     D public
open R using (Raw; `_; _∋_; op) public
