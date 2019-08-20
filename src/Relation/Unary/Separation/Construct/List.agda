{-# OPTIONS --allow-unsolved-metas #-}
module Relation.Unary.Separation.Construct.List {a} {A : Set a} where

open import Data.Product
open import Data.List
open import Data.List.Relation.Ternary.Interleaving.Propositional as I
open import Data.List.Relation.Ternary.Interleaving.Properties
open import Data.List.Relation.Binary.Equality.Propositional
open import Data.List.Relation.Binary.Permutation.Inductive

open import Relation.Binary.PropositionalEquality as P hiding ([_])
open import Relation.Unary hiding (_∈_; _⊢_)
open import Relation.Unary.Separation

open RawSep ⦃...⦄
open RawUnitalSep ⦃...⦄
open IsConcattative ⦃...⦄
open IsUnitalSep ⦃...⦄
open IsSep ⦃...⦄

private
  C = List A

instance separation : RawSep C
separation = record { _⊎_≣_ = Interleaving }

instance unital' : RawUnitalSep C
unital' = record { ε = [] ; sep = separation }

instance ctx-has-sep : IsSep separation
ctx-has-sep = record
  { ⊎-comm = I.swap
  ; ⊎-assoc = {!!}
  }

instance ctx-hasUnitalSep : IsUnitalSep _
IsUnitalSep.unital ctx-hasUnitalSep                    = unital'
IsUnitalSep.isSep ctx-hasUnitalSep                     = ctx-has-sep
IsUnitalSep.⊎-identityˡ ctx-hasUnitalSep refl          = right (≡⇒≋ P.refl)
IsUnitalSep.⊎-identity⁻ˡ ctx-hasUnitalSep []           = refl
IsUnitalSep.⊎-identity⁻ˡ ctx-hasUnitalSep (refl ∷ʳ px) = cong (_ ∷_) (⊎-identity⁻ˡ px)

instance ctx-concattative : IsConcattative _
ctx-concattative = record
  { sep = separation
  ; _∙_ = _++_
  ; ⊎-∙ = λ {Φₗ} {Φᵣ} → ++-disjoint (left (≡⇒≋ P.refl)) (right (≡⇒≋ P.refl))
  }

instance ctx-resource : MonoidalSep _ _
ctx-resource = record
  { set         = record { isEquivalence = ↭-isEquivalence }
  ; isUnitalSep = ctx-hasUnitalSep
  ; isConcat    = ctx-concattative }

{- We can split All P xs over a split of xs -}
module All {v} {V : A → Set v} where

  open import Data.List.All

  all-split : ∀ {Γ₁ Γ₂ Γ} → Γ₁ ⊎ Γ₂ ≣ Γ → All V Γ → All V Γ₁ × All V Γ₂
  all-split [] [] = [] , []
  all-split (consˡ s) (px ∷ vs) = let xs , ys = all-split s vs in px ∷ xs , ys
  all-split (consʳ s) (px ∷ vs) = let xs , ys = all-split s vs in xs , px ∷ ys

{- This gives rise to a notion of linear, typed environments -}
module LinearEnv {v} {V : A → Pred C v} where

  Env = Allstar V

  env-∙ : ∀ {Γ₁ Γ₂} → ∀[ Env Γ₁ ✴ Env Γ₂ ⇒ Env (Γ₁ ∙ Γ₂) ] 
  env-∙ (nil refl ×⟨ s ⟩ env₂) rewrite ⊎-identity⁻ˡ s = env₂
  env-∙ (cons (v ×⟨ s ⟩ env₁) ×⟨ s' ⟩ env₂) =
    let _ , eq₁ , eq₂ = ⊎-assoc s s' in
    cons (v ×⟨ eq₁ ⟩ (env-∙ (env₁ ×⟨ eq₂ ⟩ env₂)))

  -- Environments can be split along context splittings
  env-split : ∀ {Γ₁ Γ₂ Γ} → Γ₁ ⊎ Γ₂ ≣ Γ → ∀[ Env Γ ⇒ Env Γ₁ ✴ Env Γ₂ ] 
  env-split [] (nil refl) = (nil refl) ×⟨ ⊎-identityˡ refl ⟩ (nil refl)
  env-split (refl ∷ˡ s) (px :⟨ σ₁ ⟩: sx) with env-split s sx
  ... | l ×⟨ σ₂ ⟩ r with ⊎-unassoc σ₁ σ₂
  ... | (Δ , p , q) = cons (px ×⟨ p ⟩ l) ×⟨ q ⟩ r
  env-split (refl ∷ʳ s) (px :⟨ σ₁ ⟩: sx) with env-split s sx
  ... | l ×⟨ σ₂ ⟩ r with ⊎-assoc σ₂ (⊎-comm σ₁)
  ... | (Δ , p , q) = l ×⟨ p ⟩ (cons (px ×⟨ ⊎-comm q ⟩ r))
