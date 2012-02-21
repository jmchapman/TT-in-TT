module Syntax where

data Con : Set
data Ty : Con → Set
data Tm : (Γ : Con) → Ty Γ → Set
data Tms : Con → Con → Set

--data _≡Con_ : Con → Con → Set
--data _≡Ty_  : ∀{Γ} → Ty Γ → Ty Γ → Set
data _≡Tm_ : ∀{Γ A} → Tm Γ A → Tm Γ A → Set
data _≡Tms_ : ∀{Γ Δ} → Tms Γ Δ → Tms Γ Δ → Set

infix 4 _·_

data Con where
  ε : Con
  _·_ : (Γ : Con) → Ty Γ → Con

data Ty where
  U    : ∀{Γ} → Ty Γ
  El   : ∀{Γ} → Tm Γ U → Ty Γ
  Π    : ∀{Γ}(A : Ty Γ)(B : Ty (Γ · A)) → Ty Γ
  _[_] : ∀{Γ Δ} → Ty Γ → Tms Δ Γ → Ty Δ
--  _<_> : ∀{Γ Δ} → Ty Γ → Δ ≡Con Γ → Ty Δ

data Tms where
  ↑ : ∀{Γ} A → Tms (Γ · A) Γ
  id : ∀{Γ} → Tms Γ Γ
  _•_ : ∀{Θ Γ Δ} → Tms Γ Δ → Tms Θ Γ → Tms Θ Δ
  ε : ∀{Γ} → Tms Γ ε
  _·_ : ∀{Γ Δ A} → (γ : Tms Γ Δ) → Tm Γ (A [ γ ]) → Tms Γ (Δ · A)

data Tm where
  vz   : ∀{Γ A} → Tm (Γ · A) (A [ ↑ A ])
  _[_] : ∀{Γ Δ A} → Tm Γ A → (γ : Tms Δ Γ) → Tm Δ (A [ γ ])
  lam  : ∀{Γ A B} → Tm (Γ · A) B → Tm Γ (Π A B)
  app  : ∀{Γ A B} → Tm Γ (Π A B) → Tm (Γ · A) B
  _<_> : ∀{Γ Δ A}{γ γ' : Tms Δ Γ} → γ ≡Tms γ' → Tm Δ (A [ γ ]) → Tm Δ (A [ γ' ]) -- map


{-
data _≡Con_ where
  ε : ε ≡Con ε
  _·_ : ∀{Γ Γ'}{A : Ty Γ}{A' : Ty Γ'}(p : Γ ≡Con Γ') → A ≡Ty A' < p > -> (Γ · A) ≡Con (Γ' · A')
  refl : ∀{Γ} → Γ ≡Con Γ
  trans : ∀{Γ Δ Θ} → Δ ≡Con Θ → Γ ≡Con Δ → Γ ≡Con Θ
-}
{-
xx : ∀{Γ A A' } → A ≡Ty A' → (Γ · A) ≡Con (Γ · A')

data _≡Ty_ where
  U : ∀{Γ} → U {Γ} ≡Ty U
  El : ∀{Γ u u'} → u ≡Tm u' → El {Γ} u ≡Ty El u'
  Π : ∀{Γ}{A A' : Ty Γ}{B B'}(p : A ≡Ty A') → B ≡Ty (B' < xx p >) → Π A B ≡Ty Π A' B'
  _[_] : ∀{Γ Δ}{A A' : Ty Γ}{γ γ' : Tms Δ Γ} → A ≡Ty A' → γ ≡Tms γ' → A [ γ ] ≡Ty A' [ γ' ]
  refl : ∀{Γ}{A : Ty Γ} → A ≡Ty A
  sym : ∀{Γ}{A B : Ty Γ} → A ≡Ty B → B ≡Ty A
  trans : ∀{Γ}{A B C : Ty Γ} → B ≡Ty C → A ≡Ty B → A ≡Ty C
  <refl> : ∀{Γ}{A : Ty Γ} → A ≡Ty (A < refl >)
  <trans> : ∀{Γ Δ Θ}{A : Ty Θ}(p : Δ ≡Con Θ)(q  : Γ  ≡Con Δ) → A < trans p q > ≡Ty A < p > < q >
-}
data _≡Tm_ where

data _≡Tms_ where
--  ↑ : ∀{Γ A A'} → A ≡Ty A' → ↑ A ≡Tms ↑ A'


--xx p = refl · trans <refl> p

--
weak : ∀{Γ A B} → Tm Γ B → Tm (Γ · A) (B [ ↑ A ])
weak t = t [ ↑ _ ]

` : ∀{Γ A} → Tm Γ A → Tms Γ (Γ · A)
` t = id · t [ id ] 

_$_ : ∀{Γ A B} → Tm Γ (Π A B) → (u : Tm Γ A) → Tm Γ (B [ ` u ])
t $ u = app t [ ` u ]

