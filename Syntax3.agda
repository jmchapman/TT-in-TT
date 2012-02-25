module Syntax3 where

--open import Relation.Binary.PropositionalEquality

data Con : Set
data Ty : Con → Set
data Tm : ∀ Γ → Ty Γ → Set
data Sub : Con → Con → Set

data _≡Con_ : Con → Con → Set 
data _≡Sub_ : ∀{Γ Δ} → Sub Γ Δ → Sub Γ Δ → Set 
data [_]_≡Ty_ : ∀ {Γ Γ'} → .(Γ ≡Con Γ') → Ty Γ → Ty Γ' → Set 
data [_⊢_]_≡Tm_ : ∀{Γ Γ' σ σ'}.(γ : Γ ≡Con Γ') → .([ γ ] σ ≡Ty σ')
  → Tm Γ σ → Tm Γ' σ' → Set

infix 4 _≡Con_
infix 6 _·_

data Con where
  ε : Con
  _·_ : (Γ : Con) → Ty Γ → Con

data _≡Con_ where
  ε : ε ≡Con ε
  _·_ : ∀ {Γ Γ' σ σ'} → .(γ : Γ ≡Con Γ') → .([ γ ] σ ≡Ty σ') → Γ · σ ≡Con Γ' · σ' 

reflCon : ∀ {Γ} → Γ ≡Con Γ
symCon : ∀ {Γ Δ} → Γ ≡Con Δ → Δ ≡Con Γ
transCon : ∀{Γ Δ Θ} → Δ ≡Con Θ → Γ ≡Con Δ → Γ ≡Con Θ

data Ty where
  U    : ∀{Γ} → Ty Γ
  El   : ∀{Γ} → Tm Γ U → Ty Γ
  Π    : ∀{Γ} σ → Ty (Γ · σ) → Ty Γ
--  _<_> : ∀{Γ Δ} → Ty Δ → .(Γ ≡Con Δ) → Ty Γ


Uaux : ∀ {Γ Γ'}{γ : Γ ≡Con Γ'} → [ γ ] U ≡Ty U

data [_]_≡Ty_ where
  U : ∀ {Γ Γ'}{γ : Γ ≡Con Γ'} → [ γ ] U ≡Ty U
  El : ∀ {Γ Γ'}{t : Tm Γ U}{t' : Tm Γ' U}{γ : Γ ≡Con Γ'} 
       → [ γ ⊢ Uaux {γ = γ}  ] t ≡Tm t' 
       → [ γ ] (El t) ≡Ty (El t')
  Π : ∀ {Γ Γ' σ σ' τ τ'}{γ : Γ ≡Con Γ'}(s : [ γ ] σ ≡Ty σ')
        (t : [ γ · s ] τ ≡Ty τ') → [ γ ] (Π σ τ) ≡Ty (Π σ' τ')

Uaux {Γ}{Γ'}{γ} = U{Γ}{Γ'}{γ}

reflTy : ∀ {Γ}{σ : Ty Γ} → [ reflCon ] σ ≡Ty σ
symTy : ∀ {Γ Δ σ τ}(γ : Γ ≡Con Δ) → [ γ ] σ ≡Ty τ → [ symCon γ ] τ ≡Ty σ 
transTy : ∀{Γ Δ Θ σ τ ρ}(γ : Δ ≡Con Θ)(δ : Γ ≡Con Δ)
                → [ γ ] τ ≡Ty ρ → [ δ ] σ ≡Ty τ → [ transCon γ δ ] σ ≡Ty ρ 

reflCon {ε} = ε
reflCon {Γ · σ} = reflCon · reflTy

symCon ε = ε
symCon (γ · s) = symCon γ · symTy γ s

transCon ε ε = ε
transCon (γ · s) (δ · t) = transCon γ δ · transTy γ δ s t

_[_]Ty : ∀{Γ Δ} → Ty Δ → Sub Γ Δ → Ty Γ

data Sub where
  id : ∀{Γ} → Sub Γ Γ
  _•_ : ∀{B Γ Δ} → Sub Γ Δ → Sub B Γ → Sub B Δ
  ε : ∀{Γ} → Sub Γ ε
  ↑ : ∀{Γ σ} → Sub (Γ · σ) Γ
  _·_ : ∀{Γ Δ σ} → (γ : Sub Γ Δ) → Tm Γ (σ [ γ ]Ty) → Sub Γ (Δ · σ)

data Tm where
  vz   : ∀{Γ σ} → Tm (Γ · σ) (σ [ ↑ ]Ty)
  _[_] : ∀{Γ Δ σ} → Tm Δ σ → (γ : Sub Γ Δ) → Tm Γ (σ [ γ ]Ty)
  lam  : ∀{Γ σ τ} → Tm (Γ · σ) τ → Tm Γ (Π σ τ)
  app  : ∀{Γ σ τ} → Tm Γ (Π σ τ) → Tm (Γ · σ) τ
  _<_> : ∀{Γ Γ' σ σ'} → Tm Γ σ → {γ : Γ ≡Con Γ'} → [ γ ] σ ≡Ty σ' → Tm Γ' σ' 

_+_ : ∀ {Γ Δ}(ts : Sub Γ Δ)(σ : Ty Δ) → Sub (Γ · σ [ ts ]Ty) (Δ · σ)
ts + σ = {!!}

U[] : ∀ {Γ Δ}{ts : Sub Γ Δ} → Tm Γ (U [ ts ]Ty) → Tm Γ U

U [ ts ]Ty = U
El t [ ts ]Ty = El (U[]  (t [ ts ]))
Π σ τ [ ts ]Ty = Π (σ [ ts ]Ty) (τ [ ts + σ ]Ty)

U[] t = t

_<_>Ty : ∀{Γ Δ} → Ty Δ → .(Γ ≡Con Δ) → Ty Γ

U<> : ∀ {Γ Δ}.{δ : Γ ≡Con Δ} → Tm Γ (U < δ >Ty) → Tm Γ U

U < γ >Ty = U
El t < γ >Ty = {!!}
Π σ τ < γ >Ty = {!!}

U<> t = t

{-
  _<_> : ∀{Γ Δ σ}{γ γ' : Sub Γ Δ} → 
         Tm Γ (σ [ γ ]) → .(γ ≡Sub γ') →  Tm Γ (σ [ γ' ]) -- map a.k.a. subst
  -- resp
-}
data _≡Sub_ where

{-
   -- computation rules
   
   -- categorical laws
   lid : ∀{Γ Δ}{γ : Sub Γ Δ} → γ • id ≡Sub γ
   rid : ∀{Γ Δ}{γ : Sub Γ Δ} → id • γ ≡Sub γ
   ass : ∀{A B Γ Δ}{α  : Sub Γ Δ}{β : Sub B Γ}{γ : Sub A B} →
         α • (β • γ) ≡Sub (α • β) • γ

   -- product laws
   ·β₁ :  ∀{Γ Δ σ}{γ : Sub Γ Δ}{a : Tm Γ (σ [ γ ])} → ↑ • (γ · a) ≡Sub γ 

   -- congruences
   _•_ : ∀{Θ Γ Δ}{γ γ' : Sub Γ Δ}{δ δ' : Sub Θ Γ} → γ ≡Sub γ' → δ ≡Sub δ'  → 
         γ • δ ≡Sub γ' • δ' -- H & L have δ = δ'
   _·_ : ∀{Γ Δ σ}{γ γ' : Sub Γ Δ}{t : Tm Γ (σ [ γ ])}{t' : Tm Γ (σ [ γ' ])} →
         (p : γ ≡Sub γ') → t < p > ≡Tm t' → γ · t ≡Sub γ' · t'

   -- equivalence closure
   refl  : ∀{Γ Δ}{γ : Sub Γ Δ} → γ ≡Sub γ
   sym   : ∀{Γ Δ}{γ γ' : Sub Γ Δ} → γ ≡Sub γ' → γ' ≡Sub γ
   trans : ∀{Γ Δ}{γ γ' γ'' : Sub Γ Δ} → γ' ≡Sub γ'' → γ ≡Sub γ' → γ' ≡Sub γ''
-}

data [_⊢_]_≡Tm_ where
  reflTm : ∀ {Γ}{σ}{t : Tm Γ σ} → [ reflCon ⊢ reflTy ] t ≡Tm t
  symTm : ∀{Γ Γ' σ σ' t t'}{γ : Γ ≡Con Γ'}{s : [ γ ] σ ≡Ty σ'} 
              → [ γ ⊢ s ] t ≡Tm t' → [ symCon γ ⊢ symTy γ s ] t' ≡Tm t

reflTy {Γ} {U} = U {γ = reflCon {Γ}}
reflTy {Γ} {El t} = El {γ = reflCon} reflTm
reflTy {Γ} {Π σ τ} = Π {γ = reflCon} reflTy reflTy

symTy γ U = U {γ = symCon γ}
symTy γ (El t) = El {γ = symCon γ} (symTm {γ = γ} {s = U {γ = γ}} t)
symTy γ (Π s t) = Π {γ = symCon γ} (symTy γ s) (symTy (γ · s) t)

transTy s t = {!!}


{-
   -- computation rules
   beta : ∀{Γ σ τ}{t : Tm (Γ · σ) τ} → app (lam t) ≡Tm t
   eta  : ∀{Γ σ τ}{t : Tm Γ (Π σ τ)} → lam (app t) ≡Tm t
   
   -- product laws
--   β₂ : ∀{Γ Δ σ} → (γ : Sub Γ Δ)(a : Tm Γ (σ [ γ ])) → vz [ γ · a ] ≡Tm a
--  γ · a : Sub Γ (Δ · σ)
-- vz [ γ · a ] : σ [ ↑ ] [ γ · a ] 

   -- congruences
   _[_] : ∀{Γ Δ σ}{t t' : Tm Δ σ}{γ γ' : Sub Γ Δ} →
          t ≡Tm t' → (p : γ ≡Sub γ') → (t [ γ ]) < p > ≡Tm t' [ γ' ]
   lam  : ∀{Γ σ τ}{t t' : Tm (Γ · σ) τ} → lam t ≡Tm lam t'
   app  : ∀{Γ σ τ}{t t' : Tm Γ (Π σ τ)} → app t ≡Tm app t'

   -- equivalence closure
   refl  : ∀{Γ σ}{t : Tm Γ σ} → t ≡Tm t
   sym   : ∀{Γ σ}{t t' : Tm Γ σ} → t ≡Tm t' → t' ≡Tm t 
   trans : ∀{Γ σ}{t t' t'' : Tm Γ σ} → t' ≡Tm t'' → t ≡Tm t' → t ≡Tm t''
-}


{-
--
weak : ∀{Γ σ τ} → Tm Γ τ → Tm (Γ · σ) (τ [ ↑ ])
weak t = t [ ↑ ]

` : ∀{Γ σ} → Tm Γ σ → Sub Γ (Γ · σ)
` t = id · t [ id ] 

_$_ : ∀{Γ σ τ} → Tm Γ (Π σ τ) → (u : Tm Γ σ) → Tm Γ (τ [ ` u ])
t $ u = app t [ ` u ]
-}
