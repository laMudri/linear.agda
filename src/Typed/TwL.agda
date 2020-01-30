module Typed.TwL where

open import Prelude
open import Function
open import Level
open import Category.Monad
open import Data.Bool renaming (true to left; false to right)
open import Data.List.Relation.Ternary.Interleaving.Propositional
import Data.Product as ×

open import Relation.Unary.PredicateTransformer using (PT; Pt)
open import Relation.Ternary.Separation.Construct.Unit
open import Relation.Ternary.Separation.Allstar
open import Relation.Ternary.Separation.Monad
open import Relation.Ternary.Separation.Morphisms
open import Relation.Ternary.Separation.Monad.Reader
open import Relation.Ternary.Separation.Monad.Delay

data Ty : Set where
  unit : Ty
  _⊸_ _⊗_ : (a b : Ty) → Ty

Ctx  = List Ty
Ctx² = Ctx × Ctx
Ctx²T = Ctx² → Ctx²

open import Relation.Ternary.Separation.Construct.TwL (setoid Ctx)

infixr 20 _◂_
_◂_ : Ty → Ctx²T → Ctx²T
(x ◂ f) ΓΔ = ×.map (x ∷_) id (f ΓΔ)

variable a b c : Ty
variable ℓv  : Level
variable τ   : Set ℓv
variable Γ Γ₁ Γ₂ Γ₃ : List τ

-- Γ is being left alone, whereas [ a ] is in the right place.
Var : Ty → Pred (Ctx × Ctx) _
Var a (Γa , Γ) = Interleaving Γ [ a ] Γa

data Exp : Ty → Ctx × Ctx → Set where
  -- variables
  var : ∀[ Var a ⇒ Exp a ]

  -- the tensor unit
  tt      : ∀[ I ⇒ Exp unit ]
  letunit : ∀[ Exp unit ✴ Exp a ⇒ Exp a ]

  -- tensor products
  pair    : ∀[ Exp a ✴ Exp b ⇒ Exp (a ⊗ b) ]
  letprod : ∀[ Exp (a ⊗ b) ✴ (a ◂ b ◂ id ⊢ Exp c) ⇒ Exp c ]

  -- functions
  lam : ∀[ (a ◂ id ⊢ Exp b) ⇒ Exp (a ⊸ b) ]
  ap  : ∀[ Exp (a ⊸ b) ✴ Exp a ⇒ Exp b ]

-- Deep id on the unit type
test0 : Exp (unit ⊸ unit) ([] , [])
test0 = lam (letunit (var (consʳ []) ×⟨ refl , refl , refl ⟩ tt refl))

-- Same again, with a pattern synonym _×⟨⟩_ (R.T.S.Construct.TwL)
-- If the var subterm is left out, agda2-auto can work it out.
test1 : Exp (unit ⊸ unit) ([] , [])
test1 = lam (letunit (var (consʳ []) ×⟨⟩ tt refl))

Closed : Ty → Set
Closed a = Exp a ([] , [])

-- Swapping a pair
-- Again, agda2-auto is good at variables,
-- if you tell it to use the `var` constructor.
test2 : Closed ((a ⊗ b) ⊸ (b ⊗ a))
test2 = lam (letprod (var (consʳ [])
                 ×⟨⟩ pair (var (consˡ (consʳ [])) ×⟨⟩ var (consʳ []))))
