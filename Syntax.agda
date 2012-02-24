module Syntax where

data Con : Set
data Ty : Con → Set
data Tm : ∀ Γ → Ty Γ → Set
data Sub : Con → Con → Set

data _≡Tm_ : ∀{Γ σ} → Tm Γ σ → Tm Γ σ → Set
data _≡Sub_ : ∀{Γ Δ} → Sub Γ Δ → Sub Γ Δ → Set

infix 1 _≡Tm_
infix 1 _≡Sub_

data Con where
  ε : Con
  _·_ : (Γ : Con) → Ty Γ → Con

data Ty where
  U    : ∀{Γ} → Ty Γ
  El   : ∀{Γ} → Tm Γ U → Ty Γ
  Π    : ∀{Γ} σ → Ty (Γ · σ) → Ty Γ
  _[_] : ∀{Γ Δ} → Ty Δ → Sub Γ Δ → Ty Γ

data Sub where
  ↑ : ∀{Γ σ} → Sub (Γ · σ) Γ
  id : ∀{Γ} → Sub Γ Γ
  _•_ : ∀{B Γ Δ} → Sub Γ Δ → Sub B Γ → Sub B Δ
  ε : ∀{Γ} → Sub Γ ε
  _·_ : ∀{Γ Δ σ} → (γ : Sub Γ Δ) → Tm Γ (σ [ γ ]) → Sub Γ (Δ · σ)

data Tm where
  vz   : ∀{Γ σ} → Tm (Γ · σ) (σ [ ↑ ])
  _[_] : ∀{Γ Δ σ} → Tm Δ σ → (γ : Sub Γ Δ) → Tm Γ (σ [ γ ])
  lam  : ∀{Γ σ τ} → Tm (Γ · σ) τ → Tm Γ (Π σ τ)
  app  : ∀{Γ σ τ} → Tm Γ (Π σ τ) → Tm (Γ · σ) τ
  _<_> : ∀{Γ Δ σ}{γ γ' : Sub Γ Δ} → 
         Tm Γ (σ [ γ ]) → γ ≡Sub γ' →  Tm Γ (σ [ γ' ]) -- map a.k.a. subst

data _≡Sub_ where
   -- computation rules
   
   -- categorical laws
   lid : ∀{Γ Δ}{γ : Sub Γ Δ} → γ • id ≡Sub γ
   rid : ∀{Γ Δ}{γ : Sub Γ Δ} → id • γ ≡Sub γ
   ass : ∀{A B Γ Δ}{α  : Sub Γ Δ}{β : Sub B Γ}{γ : Sub A B} →
         α • (β • γ) ≡Sub (α • β) • γ

   -- congruences
   _•_ : ∀{Θ Γ Δ}{γ γ' : Sub Γ Δ}{δ δ' : Sub Θ Γ} → γ ≡Sub γ' → δ ≡Sub δ'  → 
         γ • δ ≡Sub γ' • δ' -- H & L have δ = δ'
   _·_ : ∀{Γ Δ σ}{γ γ' : Sub Γ Δ}{t : Tm Γ (σ [ γ ])}{t' : Tm Γ (σ [ γ' ])} →
         (p : γ ≡Sub γ') → t < p > ≡Tm t' → γ · t ≡Sub γ' · t'

   -- equivalence closure
   refl  : ∀{Γ Δ}{γ : Sub Γ Δ} → γ ≡Sub γ
   sym   : ∀{Γ Δ}{γ γ' : Sub Γ Δ} → γ ≡Sub γ' → γ' ≡Sub γ
   trans : ∀{Γ Δ}{γ γ' γ'' : Sub Γ Δ} → γ' ≡Sub γ'' → γ ≡Sub γ' → γ' ≡Sub γ''


data _≡Tm_ where
   -- computation rules
   beta : ∀{Γ σ τ}{t : Tm (Γ · σ) τ} → app (lam t) ≡Tm t
   eta  : ∀{Γ σ τ}{t : Tm Γ (Π σ τ)} → lam (app t) ≡Tm t
   
   -- congruences
   _[_] : ∀{Γ Δ σ}{t t' : Tm Δ σ}{γ γ' : Sub Γ Δ} →
          t ≡Tm t' → (p : γ ≡Sub γ') → (t [ γ ]) < p > ≡Tm t' [ γ' ]
   lam  : ∀{Γ σ τ}{t t' : Tm (Γ · σ) τ} → lam t ≡Tm lam t'
   app  : ∀{Γ σ τ}{t t' : Tm Γ (Π σ τ)} → app t ≡Tm app t'

   -- equivalence closure
   refl  : ∀{Γ σ}{t : Tm Γ σ} → t ≡Tm t
   sym   : ∀{Γ σ}{t t' : Tm Γ σ} → t ≡Tm t' → t' ≡Tm t 
   trans : ∀{Γ σ}{t t' t'' : Tm Γ σ} → t' ≡Tm t'' → t ≡Tm t' → t ≡Tm t''

--
weak : ∀{Γ σ τ} → Tm Γ τ → Tm (Γ · σ) (τ [ ↑ ])
weak t = t [ ↑ ]

` : ∀{Γ σ} → Tm Γ σ → Sub Γ (Γ · σ)
` t = id · t [ id ] 

_$_ : ∀{Γ σ τ} → Tm Γ (Π σ τ) → (u : Tm Γ σ) → Tm Γ (τ [ ` u ])
t $ u = app t [ ` u ]

