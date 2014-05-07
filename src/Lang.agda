module Lang where

open import Data.Nat
open import Data.Bool
open import Data.Product

infix  3 _∈_
infixr 4 _∷_

infix  3 _⊢_

data var : ℕ → ℕ → Set where
  Z : ∀ {n} → var zero (suc n)
  S : ∀ {m n} → var m n → var (suc m) (suc n)

data type (n : ℕ) : Set where
  -- source types
  s-bool : type n
  _s⇒_ : type n → type n → type n

  -- target types
  t-var : ∀ {m} → var m n → type n
  t-bool : type n
  _t×_ : type n → type n → type n
  _t⇒_ : type n → type n → type n
  
data tenv : ℕ → Set where
  • : tenv zero
  _∷_ : ∀ {n} → type n → tenv n → tenv (suc n)
  
data is-s-type (n : ℕ) : type n → Set where
  is-s-bool : is-s-type n s-bool
  is-s-⇒ : ∀ τ₁ τ₂ → is-s-type n τ₁ → is-s-type n τ₂ → is-s-type n (τ₁ t⇒ τ₂)
  
data is-t-type (n : ℕ) : type n → Set where
  is-t-var : ∀ {m} (p : var m n) → is-t-type n (t-var p)
  is-t-bool : is-t-type n t-bool
  is-t-× : ∀ τ₁ τ₂ → is-t-type n τ₁ → is-t-type n τ₂ → is-t-type n (τ₁ t× τ₂)
  is-t-⇒ : ∀ τ₁ τ₂ → is-t-type n τ₁ → is-t-type n τ₂ → is-t-type n (τ₂ t⇒ τ₂)
  
data ctx (n : ℕ) : Set where
  • : ctx n
  _∷_ : type n → ctx n → ctx n
  
data _∈_ {n : ℕ} : type n → ctx n → Set where
  hd : ∀ {Γ} {τ : type n} → τ ∈ τ ∷ Γ
  tl : ∀ {Γ} {τ₁ τ₂ : type n} → τ₁ ∈ Γ → τ₁ ∈ τ₂ ∷ Γ
  
data _⊢_ {n : ℕ} : ctx n → type n → Set where
  s-var : ∀ {Γ τ} → is-s-type n τ → τ ∈ Γ → Γ ⊢ τ
  s-true : ∀ {Γ} → Γ ⊢ t-bool
  s-false : ∀ {Γ} → Γ ⊢ t-bool
  s-λ : ∀ {Γ τ₁ τ₂} → is-s-type n τ₁ → is-s-type n τ₂ → τ₁ ∷ Γ ⊢ τ₂ → Γ ⊢ τ₁ s⇒ τ₂
  s-if : ∀ {Γ τ} → is-s-type n τ → Γ ⊢ t-bool → Γ ⊢ τ → Γ ⊢ τ → Γ ⊢ τ
  s-⊙ : ∀ {Γ τ₁ τ₂} → is-s-type n τ₁ → is-s-type n τ₂ → Γ ⊢ τ₁ s⇒ τ₂ → Γ ⊢ τ₁ → Γ ⊢ τ₂
  
  t-var : ∀ {Γ τ} → is-t-type n τ → τ ∈ Γ → Γ ⊢ τ
  t-true : ∀ {Γ} → Γ ⊢ t-bool
  t-false : ∀ {Γ} → Γ ⊢ t-bool
  t-, : ∀ {Γ τ₁ τ₂} → is-t-type n τ₁ → is-t-type n τ₂ → Γ ⊢ τ₁ → Γ ⊢ τ₂ → Γ ⊢ τ₁ t× τ₂
  t-λ : ∀ {Γ τ₁ τ₂} → is-t-type n τ₁ → is-t-type n τ₂ → τ₁ ∷ Γ ⊢ τ₂ → Γ ⊢ τ₁ t⇒ τ₂
  t-if : ∀ {Γ τ} → is-t-type n τ → Γ ⊢ t-bool → Γ ⊢ τ → Γ ⊢ τ → Γ ⊢ τ
  t-π₁ : ∀ {Γ τ₁ τ₂} → is-t-type n τ₁ → is-t-type n τ₂ → Γ ⊢ τ₁ t× τ₂ → Γ ⊢ τ₁
  t-π₂ : ∀ {Γ τ₁ τ₂} → is-t-type n τ₁ → is-t-type n τ₂ → Γ ⊢ τ₁ t× τ₂ → Γ ⊢ τ₂
  t-⊙ : ∀ {Γ τ₁ τ₂} → is-t-type n τ₁ → is-t-type n τ₂ → Γ ⊢ τ₁ t⇒ τ₂ → Γ ⊢ τ₁ → Γ ⊢ τ₂
  
data env {n : ℕ} : ctx n → ctx n → Set where
  • : ∀ Γ → env • Γ
  _∷_ : ∀ Γ₁ Γ₂ τ → Γ₂ ⊢ τ → env Γ₁ Γ₂ → env (τ ∷ Γ₁) Γ₂
  
mutual
  den-var : ∀ {n m} → tenv n → var m n → Set
  den-var {zero} {zero} • ()
  den-var {zero} {suc _} • ()
  den-var {suc n} {zero} (τ ∷ τρ) Z = den τρ τ
  den-var {suc n} {suc m} (τ ∷ τρ) (S x) = den-var τρ x

  den : ∀ {n} → tenv n → type n → Set
  den _ s-bool = Bool
  den τρ (τ₁ s⇒ τ₂) = den τρ τ₁ → den τρ τ₂
  den τρ (t-var p) = den-var τρ p
  den τρ t-bool = Bool
  den τρ (τ₁ t× τ₂) = den τρ τ₁ × den τρ τ₂
  den τρ (τ₁ t⇒ τ₂) = den τρ τ₁ → den τρ τ₂
  
data den-env {n : ℕ} (τρ : tenv n) : ctx n → Set where
  • : den-env τρ •
  _∷_ : ∀ {Γ τ} → den τρ τ → den-env τρ Γ → den-env τρ (τ ∷ Γ)
  
denote-var : ∀ {n Γ τ} {τρ : tenv n} → den-env τρ Γ → τ ∈ Γ → den τρ τ
denote-var (v ∷ ρ) hd = v
denote-var (x ∷ ρ) (tl x₁) = denote-var ρ x₁
  
denote : ∀ {n Γ τ} {τρ : tenv n} → den-env τρ Γ → Γ ⊢ τ → den τρ τ
denote ρ (s-var _ x) = denote-var ρ x
denote ρ s-true = true
denote ρ s-false = false
denote ρ (s-λ _ _ e) = λ v₁ → denote (v₁ ∷ ρ) e
denote ρ (s-if _ e te fe) = if denote ρ e then denote ρ te else denote ρ fe
denote ρ (s-⊙ _ _ fe ae) = denote ρ fe (denote ρ ae)
denote ρ (t-var _ x) = denote-var ρ x
denote ρ t-true = true
denote ρ t-false = false
denote ρ (t-, _ _ e₁ e₂) = denote ρ e₁ , denote ρ e₂
denote ρ (t-λ _ _ e) = λ v₁ → denote (v₁ ∷ ρ) e
denote ρ (t-if _ e te fe) = if denote ρ e then denote ρ te else denote ρ fe
denote ρ (t-π₁ _ _ e) = proj₁ (denote ρ e)
denote ρ (t-π₂ _ _ e) = proj₂ (denote ρ e)
denote ρ (t-⊙ _ _ fe ae) = denote ρ fe (denote ρ ae)