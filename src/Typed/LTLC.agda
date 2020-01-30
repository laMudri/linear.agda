module Typed.LTLC where

open import Prelude
open import Function
open import Level
open import Category.Monad
open import Data.Bool renaming (true to left; false to right)

open import Relation.Unary.PredicateTransformer using (PT; Pt)
open import Relation.Ternary.Separation.Construct.Unit
open import Relation.Ternary.Separation.Allstar
open import Relation.Ternary.Separation.Monad
open import Relation.Ternary.Separation.Morphisms
open import Relation.Ternary.Separation.Monad.Reader
open import Relation.Ternary.Separation.Monad.Delay

data Ty : Set where
  unit : Ty
  _⊸_ _w&_ : (a b : Ty) → Ty

open import Relation.Ternary.Separation.Construct.List Ty

Ctx  = List Ty
CtxT = List Ty → List Ty

infixr 20 _◂_
_◂_ : Ty → CtxT → CtxT
(x ◂ f) Γ = x ∷ f Γ

variable a b : Ty
variable ℓv  : Level
variable τ   : Set ℓv
variable Γ Γ₁ Γ₂ Γ₃ : List τ

data Exp : Ty → Ctx → Set where
  -- a base type
  tt       : ε[ Exp unit ]
  letunit  : ∀[ Exp unit ✴ Exp a ⇒ Exp a ]

  -- the λ-calculus
  lam : ∀[ (a ◂ id ⊢ Exp b) ⇒ Exp (a ⊸ b) ]
  ap  : ∀[ Exp (a ⊸ b) ✴ Exp a ⇒ Exp b ]
  var : ∀[ Just a ⇒ Exp a ]

  -- with products
  wth : ∀[ (Exp a ∩ Exp b) ⇒ Exp (a w& b) ]
  proj : ∀ d → ∀[ Exp (a w& b) ⇒ Exp (if d then a else b) ]

module _ {{m : MonoidalSep 0ℓ}} where
  open MonoidalSep m using (Carrier)

  CPred : Set₁
  CPred = Carrier → Set

  mutual
    Env : Ctx → CPred
    Env = Allstar Val

    data Val : Ty → CPred where
      tt    : ε[ Val unit ]
      clos  : Exp b (a ∷ Γ) → ∀[ Env Γ ⇒ Val (a ⊸ b) ]
      wth   : Exp a Γ → Exp b Γ → ∀[ Env Γ ⇒ Val (a w& b) ]

  module _ {i : Size} where
    open ReaderTransformer id-morph Val (Delay i) public
    open Monads.Monad reader-monad public

  M : Size → (Γ₁ Γ₂ : Ctx) → CPred → CPred
  M i = Reader {i}

  open Monads using (str; _&_; typed-str)

  mutual
    eval : ∀ {i} → Exp a Γ → ε[ M i Γ ε (Val a) ]

    eval tt = do
      return tt

    eval (letunit (e₁ ×⟨ Γ≺ ⟩ e₂)) = do
      tt ← frame Γ≺ (►eval e₁)
      ►eval e₂

    eval (lam e) = do
      env ← ask
      return (clos e env)

    eval (ap (f ×⟨ Γ≺ ⟩ e)) = do
      clos body env ← frame Γ≺ (►eval f)
      v ×⟨ σ ⟩ env  ← ►eval e & env
      empty         ← append (v :⟨ σ ⟩: env)
      ►eval body

    eval (var refl) = do
      lookup

    eval (wth (eₗ , eᵣ)) = do
      env ← ask
      return (wth eₗ eᵣ env)

    eval (proj left e) = do
      wth eₗ eᵣ env ← ►eval e
      empty         ← append env
      ►eval eₗ

    eval (proj right e) = do
      wth eₗ eᵣ env ← ►eval e
      empty         ← append env
      ►eval eᵣ

    ►eval : ∀ {i} → Exp a Γ → ε[ M i Γ ε (Val a) ]
    app (►eval e) E σ = later (λ where .force → app (eval e) E σ)
