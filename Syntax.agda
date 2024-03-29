module Syntax
  where

data Type : Set where
  Boolean : Type
  _⇒_ : Type → Type → Type

data Context : Set where
  ∅ : Context
  _,,_ : Context → Type → Context

-- Values of this type represent a well-typed bound variable (bound in the given typing context)
-- This is actually a kind of de Bruijn index! It just has more information than the usual numbers
data _∋_ : Context → Type → Set where
  ∋-here : ∀ {Γ A} →
    (Γ ,, A) ∋ A

  ∋-there : ∀ {Γ A B} →
    Γ ∋ A →
    (Γ ,, B) ∋ A

-- This represents a term that is well-typed with the given type in the given typing context
data Term : Context → Type → Set where
  true : ∀ {Γ} →
    Term Γ Boolean

  false : ∀ {Γ} →
    Term Γ Boolean

  V : ∀ {Γ A} →
    Γ ∋ A →
    Term Γ A

  app : ∀ {Γ A B} →
    Term Γ (A ⇒ B) →
    Term Γ A →
    Term Γ B

  lam : ∀ {Γ A B} →
    Term (Γ ,, A) B →
    Term Γ (A ⇒ B)

-- This corresponds to ∅ ⊢ λx. x : Boolean → Boolean
example1 : Term ∅ (Boolean ⇒ Boolean)
example1 = lam (V ∋-here)
