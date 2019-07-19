-- | We move the environment into the monad, getting rid of explicit env-splits.
-- To accomplish this we introduces `frame` as a primitive.
module Sessions.Semantics.Expr-02 where

open import Prelude
open import Data.Fin

open import Relation.Unary.PredicateTransformer hiding (_⊔_)

open import Sessions.Syntax.Types
open import Sessions.Syntax.Values
open import Sessions.Syntax.Expr

open import Sessions.Semantics.Expr-01 using (Cmd; F; module Free; pure; impure; Cont) public

module M where

  M : LCtx → LCtx → Pred SCtx 0ℓ → Pred SCtx 0ℓ
  M Γ₁ Γ₂ P = Env Γ₁ ─✴ F (Env Γ₂ ✴ P) 

  return : ∀ {P} → ∀[ P ⇒ M Γ Γ P ]
  return px e s = pure (e ×⟨ ⊎-comm s ⟩ px)

  bind : ∀ {P Q} → ∀[ (P ─✴ M Γ₂ Γ₃ Q) ⇒ (M Γ₁ Γ₂ P ─✴ M Γ₁ Γ₃ Q) ]
  bind f mp σ₁ env σ₂ =
    let
      _ , σ₃ , σ₄ = ⊎-assoc σ₁ σ₂
      f[e✴px]       = mp env σ₄
    in Free.f-bind (λ where
      (env ×⟨ σ₅ ⟩ px) σ₆ →
        let _ , σ₇ , σ₈ = ⊎-assoc σ₅ (⊎-comm σ₆)
        in f px (⊎-comm σ₈) env (⊎-comm σ₇)) f[e✴px] σ₃

  lift-f : ∀ {P} → ∀[ F P ⇒ M ε ε P ]
  lift-f px (nil refl) σ = Free.f-map (λ px σ' → (nil refl) ×⟨ σ' ⟩ px) px (⊎-comm σ)

  -- syntax bind f p s = p split s bind f
  syntax bind f p s = p ⟪ s ⟫= f

  frame : ∀ {P} → Γ₁ ⊎ Γ₃ ≣ Γ₂ → ∀[ M Γ₁ ε P ⇒ M Γ₂ Γ₃ P ]
  frame sep c env s =
    let
      (E₁ ×⟨ E≺ ⟩ E₂) = env-split sep env
      (Φ , eq₁ , eq₂) = ⊎-assoc E≺ (⊎-comm s)
    in bind
      (λ px s' → λ where (nil refl) s'' → pure $ E₂ ×⟨ subst (_ ⊎ _ ≣_) (⊎-identity⁻ʳ s'') s' ⟩ px)
      c eq₂ E₁ (⊎-comm eq₁)

  asks : ∀ {P} → ∀[ (Env Γ ─✴ P) ⇒ M Γ ε P ]
  asks f env σ =
    let px = f env σ
    in pure (nil refl ×⟨ ⊎-identityˡ refl ⟩ px)

  prepend : ∀[ Env Γ₁ ⇒ M Γ₂ (Γ₁ ∙ Γ₂) Emp ]
  prepend env₁ env₂ s = pure $ env-∙ (env₁ ×⟨ s ⟩ env₂) ×⟨ ⊎-identityʳ refl ⟩ refl

  append : ∀[ Env Γ₁ ⇒ M Γ₂ (Γ₂ ∙ Γ₁) Emp ]
  append env₁ env₂ s = pure $ env-∙ (env₂ ×⟨ ⊎-comm s ⟩ env₁) ×⟨ ⊎-identityʳ refl ⟩ refl

module _ where
  open M

  {-# TERMINATING #-}
  eval′ : Exp a Γ → M Γ ε (Val a) ε
  eval′ (var refl) = asks (λ where
    (cons (px ×⟨ σ₁ ⟩ nil refl)) σ₂ →
      subst (Val _) (trans (⊎-identity⁻ʳ σ₁) (⊎-identity⁻ˡ σ₂)) px)

  eval′ (unit refl) =
    return (tt refl)

  eval′ (λₗ a e) =
    asks λ env σ →
      clos (closure e (subst (Env _) (⊎-identity⁻ˡ σ) env))

  eval′ (app (f ×⟨ Γ≺ ⟩ e)) =
    frame Γ≺ (eval′ f) ⟪ ⊎-identityʳ refl ⟫= λ where
      (clos (closure body closure-env)) s → eval′ e ⟪ ⊎-comm s ⟫= λ where
        v σ₁ → append (singleton v) ⟪ σ₁ ⟫= λ where
          refl σ₂ → append closure-env ⟪ ⊎-comm σ₂ ⟫= λ where
            refl σ₃ → subst (M _ _ _) (⊎-identity⁻ˡ σ₃) (eval′ body)

  eval′ (pairs (fst ×⟨ Γ≺ ⟩ snd)) =
    frame Γ≺ (eval′ fst) ⟪ ⊎-identityˡ refl ⟫= λ where
      v σ₁ → eval′ snd ⟪ ⊎-comm σ₁ ⟫= λ where
        w σ₂ → return (pairs (v ×⟨ σ₂ ⟩ w))

  eval′ (letpair (e ×⟨ Γ≺ ⟩ body)) =
    frame Γ≺ (eval′ e) ⟪ ⊎-identityˡ refl ⟫= λ where
      (pairs (px ×⟨ σ₁ ⟩ qx)) σ₂ →
        let env' = cons (px ×⟨ σ₁ ⟩ singleton qx)
        in prepend env' ⟪ σ₂ ⟫= λ where
        refl σ₃ → subst (M _ _ _) (⊎-identity⁻ˡ σ₃) (eval′ body)

  eval′ (send (e ×⟨ Γ≺ ⟩ ch)) =
    frame Γ≺ (eval′ e) ⟪ ⊎-identityˡ refl ⟫= λ where
      v σ₁ → eval′ ch ⟪ ⊎-comm σ₁ ⟫= λ where
        (chan φ) σ₂ → lift-f (Free.send! (φ ×⟨ ⊎-comm σ₂ ⟩ v)) ⟪ ⊎-identityˡ refl ⟫= λ where
          v σ₃ → subst (M _ _ _) (⊎-identity⁻ˡ σ₃) (return (chan v))

  eval′ (recv e) =
    eval′ e ⟪ ⊎-identityˡ refl ⟫= λ where
      (chan φ) σ₁ → lift-f (Free.receive! φ) ⟪ σ₁ ⟫= λ where
        φ✴v σ₃ → subst (M _ _ _) (⊎-identity⁻ˡ σ₃) (return (pairs (⟨ chan ⟨✴⟩ id ⟩ φ✴v)))

  eval′ (fork e) =
    eval′ e ⟪ ⊎-identityˡ refl ⟫= λ where
      (clos κ) σ₁ → lift-f (Free.fork! κ) ⟪ σ₁ ⟫= λ where
        φ σ₂ → subst (M _ _ _) (⊎-identity⁻ˡ σ₂) (return (chan φ))

  eval′ (terminate e) =
    eval′ e ⟪ ⊎-identityˡ refl ⟫= λ where
      (chan φ) σ₁ → lift-f (Free.close! φ) ⟪ σ₁ ⟫=  λ where
        refl σ₂ → subst (M _ _ _) (⊎-identity⁻ˡ σ₂) (return (tt refl))

  eval : Exp a ε → F (Val a) ε
  eval e =
    Free.f-map
      (λ where (nil refl ×⟨ σ₁ ⟩ qx) σ₂ → subst (Val _) (trans (⊎-identity⁻ˡ σ₁) (⊎-identity⁻ˡ σ₂)) qx)
      (eval′ e (nil refl) (⊎-identityˡ refl)) (⊎-identityˡ refl)
