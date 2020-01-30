{-# OPTIONS --safe #-}

open import Relation.Binary

module Relation.Ternary.Separation.Construct.TwL {a} (setoid : Setoid a a)
  where

open Setoid setoid

open import Level
open import Data.Product

open import Relation.Binary.PropositionalEquality as P hiding ([_])
open import Relation.Unary hiding (_∈_; _⊢_)
open import Relation.Ternary.Separation

private C = Carrier × Carrier

I : Pred C a
I (Γ , Γ′) = Γ ≈ Γ′

_→←_∼_ : C → C → C → Set a
(Γ′ , Δ) →← (Δ′ , Θ) ∼ (Γ , Θ′) = Γ ≈ Γ′ × Δ ≈ Δ′ × Θ ≈ Θ′

instance separation : RawSep C
separation = record { _⊎_≣_ = _→←_∼_ }

infixr 10 _×⟨⟩_
pattern _×⟨⟩_ px qx = px ×⟨ refl , refl , refl ⟩ qx
