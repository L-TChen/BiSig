open import Prelude

module Category.Kleisli where

open import Category.Functor public

open Functor hiding (law); open FunctorLaw; open RawFunctor

private
  variable
    X Y Z : Type
    
record MonadLaw (T : Type → Type)
  (return : {X : Type} → X → T X)
  (_=<<_ : {X Y : Type} → (X → T Y) → T X → T Y) : Type₁ where
  field
    unit-left  : (x : T X)
      → return =<< x ≡ x
    unit-right : {f : X → T Y}
      → (x : X)
      → f =<< return x ≡ f x
    associative : (f : X → T Y) (g : Y → T Z)
      → (x : T X)
      → (λ x → g =<< f x) =<< x ≡ g =<< (f =<< x)

record Monad (T : Type → Type) : Type₁ where
  field
    return : X → T X
    _=<<_  : (X → T Y) → (T X → T Y)
    law    : MonadLaw T return _=<<_
  open MonadLaw law public

  infixr 5 _=<<_ 

  _>>=_ : T X → (X → T Y) → T Y
  m >>= f = f =<< m 

  instance
    Monad⇒Functor : Functor T
    fmap (raw Monad⇒Functor) f = (return ∘ f) =<<_
    (Functor.law Monad⇒Functor) .fmap-id   x     = unit-left x
    (Functor.law Monad⇒Functor) .fmap-comp f g x = begin
      return ∘ (g ∘ f) =<< x
        ≡⟨ cong (_=<< x) (funExt λ x → sym (unit-right (f x))) ⟩
      (return ∘ g =<<_) ∘ return ∘ f =<< x
        ≡⟨ associative (return ∘ f) (return ∘ g) x ⟩
      (λ x₁ → return (g x₁)) =<< ((λ x₁ → return (f x₁)) =<< x)
      ∎ where open ≡-Reasoning 

