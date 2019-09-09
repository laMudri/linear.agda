module Relation.Unary.Separation.Monad.State {ℓ} {T : Set ℓ} where

open import Level hiding (Lift)
open import Function using (_∘_; case_of_)
open import Relation.Binary.PropositionalEquality using (refl)
open import Relation.Unary
open import Relation.Unary.PredicateTransformer hiding (_⊔_; [_])
open import Relation.Unary.Separation
open import Relation.Unary.Separation.Construct.List
open import Relation.Unary.Separation.Construct.Product
open import Relation.Unary.Separation.Construct.Auth
open import Relation.Unary.Separation.Monad
open import Relation.Unary.Separation.Monad.Update

open import Data.Unit
open import Data.List
open import Data.Product

private
  ST = List T

module _ {V : T → Pred ST ℓ} where

  data Cell : Pred (ST × ST) ℓ where
    cell : ∀ {a Σ} → V a Σ → Cell ([ a ] , Σ)

  -- typed stores in auth
  St : Pred (Auth ST) ℓ
  St = Lift (Bigstar Cell)

  M : Pred (List T) ℓ → Pred (Auth (List T)) ℓ
  M P = St ==✴ (○ P) ✴ St

  private
    thebind : ∀ {P Q : Pred ST ℓ} → ∀[ (P ─✴[ ◌ ] M Q) ⇒[ ◌ ] (M P ─✴ St ─✴ ⤇' ((○ Q) ✴ St)) ]
    thebind f m σ₁ st σ₂ fr                  with ⊎-assoc σ₁ σ₂
    ... | m+st , σ₃ , σ₄                     with ⊎-assoc (⊎-comm σ₃) fr
    ... | _ , σ₅ , σ₆                        with update (m st σ₄) σ₅
    ... | _ , _ , σ₅' , frag px ×⟨ σ₆' ⟩ st' with ⊎-assoc (⊎-comm σ₆') σ₅'
    ... | _ , σ₇ , σ₈                        with ⊎-assoc (⊎-comm σ₆) (⊎-comm σ₈)
    ... | _ , τ₁ , neither τ₂                with ⊎-unassoc σ₇ (⊎-comm τ₁)
    ... | _ , τ₃ , τ₄                        with f px τ₂ st' (⊎-comm τ₃)
    ... | local update = update τ₄

  instance
    M-monad : Monad {I = ⊤} {j = ◌} (λ _ _ → M)
    Monad.return M-monad px st σ₂ = do
      return (frag px ×⟨ σ₂ ⟩ st )
    Monad.bind M-monad f m σ₁ st σ₂ = local λ fr → thebind f m σ₁ st σ₂ fr 