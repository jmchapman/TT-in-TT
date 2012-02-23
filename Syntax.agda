module Syntax where

data Con : Set
data Ty : Con → Set
data Tm : (Γ : Con) → Ty Γ → Set
data Sub : Con → Con → Set

data _≡Tm_ : ∀{Γ A} → Tm Γ A → Tm Γ A → Set
data _≡Sub_ : ∀{Γ Δ} → Sub Γ Δ → Sub Γ Δ → Set

infix 4 _·_

data Con where
  ε : Con
  _·_ : (Γ : Con) → Ty Γ → Con

data Ty where
  U    : ∀{Γ} → Ty Γ
  El   : ∀{Γ} → Tm Γ U → Ty Γ
  Π    : ∀{Γ}(σ : Ty Γ)(τ : Ty (Γ · σ)) → Ty Γ
  _[_] : ∀{Γ Δ} → Ty Δ → Sub Γ Δ → Ty Γ

data Sub where
  ↑ : ∀{Γ} σ → Sub (Γ · σ) Γ
  id : ∀{Γ} → Sub Γ Γ
  _•_ : ∀{Θ Γ Δ} → Sub Γ Δ → Sub Θ Γ → Sub Θ Δ
  ε : ∀{Γ} → Sub Γ ε
  _·_ : ∀{Γ Δ σ} → (γ : Sub Γ Δ) → Tm Γ (σ [ γ ]) → Sub Γ (Δ · σ)

data Tm where
  vz   : ∀{Γ σ} → Tm (Γ · σ) (σ [ ↑ σ ])
  _[_] : ∀{Γ Δ σ} → Tm Δ σ → (γ : Sub Γ Δ) → Tm Γ (σ [ γ ])
  lam  : ∀{Γ σ τ} → Tm (Γ · σ) τ → Tm Γ (Π σ τ)
  app  : ∀{Γ σ τ} → Tm Γ (Π σ τ) → Tm (Γ · σ) τ
  _<_> : ∀{Γ Δ σ}{γ γ' : Sub Γ Δ} → γ ≡Sub γ' → 
         Tm Γ (σ [ γ ]) → Tm Γ (σ [ γ' ]) -- map a.k.a. subst

data _≡Tm_ where
   β : ∀{Γ σ τ}{t : Tm (Γ · σ) τ} → app (lam t) ≡Tm t
   η : ∀{Γ σ τ}{t : Tm Γ (Π σ τ)} → lam (app t) ≡Tm t


   refl  : ∀{Γ σ}{t : Tm Γ σ} → t ≡Tm t
   sym   : ∀{Γ σ}{t t' : Tm Γ σ} → t ≡Tm t' → t' ≡Tm t
   trans : ∀{Γ σ}{t t' t'' : Tm Γ σ} → t ≡Tm t' → t' ≡Tm t'' → t ≡Tm t''

data _≡Sub_ where

--
weak : ∀{Γ σ τ} → Tm Γ τ → Tm (Γ · σ) (τ [ ↑ σ ])
weak t = t [ ↑ _ ]

` : ∀{Γ σ} → Tm Γ σ → Sub Γ (Γ · σ)
` t = id · t [ id ] 

_$_ : ∀{Γ σ τ} → Tm Γ (Π σ τ) → (u : Tm Γ σ) → Tm Γ (τ [ ` u ])
t $ u = app t [ ` u ]

