module Eval (A : Set)(B : A → Set) where

open import Data.Unit
open import Data.Product

open import Relation.Binary.HeterogeneousEquality
open import Syntax2

⟦_⟧Con : Con → Set
⟦_⟧Ty  : ∀{Γ} → Ty Γ → ⟦ Γ ⟧Con → Set
⟦_⟧Tm  : ∀{Γ σ} → Tm Γ σ → (γ : ⟦ Γ ⟧Con) → ⟦ σ ⟧Ty γ
⟦_⟧Sub : ∀{Γ Δ} → Sub Γ Δ → ⟦ Γ ⟧Con → ⟦ Δ ⟧Con

⟦_⟧Con≡ : ∀{Γ Γ' : Con} → Γ ≡ˠ Γ' → ⟦ Γ ⟧Con ≡ ⟦ Γ' ⟧Con
⟦ p ⟧Con≡ = ?
⟦_⟧Sub≡_ : ∀{Γ Γ' Δ Δ'}{γ : Sub Γ Δ}{γ' : Sub Γ' Δ'} → γ ≡ˢ γ → {!!}
⟦_⟧Sub≡_ = {!!}

⟦ ε     ⟧Con = ⊤
⟦ Γ , σ ⟧Con = Σ ⟦ Γ ⟧Con ⟦ σ ⟧Ty 

⟦_⟧U : ∀{Γ} → Tm Γ U → ⟦ Γ ⟧Con  → A

⟦ coe⁺ σ p  ⟧Ty γ = {!!}
⟦ σ [ ts ]⁺ ⟧Ty γ = ⟦ σ ⟧Ty (⟦ ts ⟧Sub γ)
⟦ U         ⟧Ty γ = A
⟦ El σ      ⟧Ty γ = B (⟦ σ ⟧U γ) 
⟦ Π σ  τ    ⟧Ty γ = (x : ⟦ σ ⟧Ty γ) → ⟦ τ ⟧Ty (γ , x) 

⟦ u ⟧U = ⟦ u ⟧Tm

⟦ coe t p  ⟧Tm γ       = {!!}
⟦ t [ ts ] ⟧Tm γ       = ⟦ t ⟧Tm (⟦ ts ⟧Sub γ)
⟦ top      ⟧Tm (γ , v) = {!!}
⟦ λt t     ⟧Tm γ       = λ v → ⟦ t ⟧Tm (γ , v)
⟦ app t    ⟧Tm (γ , v) = ⟦ t ⟧Tm γ v 

⟦ coeˢ ts p q ⟧Sub γ      = {!!}
⟦ ts • ts'    ⟧Sub γ      = ⟦ ts ⟧Sub (⟦ ts' ⟧Sub γ)
⟦ id          ⟧Sub γ      = γ
⟦ pop σ       ⟧Sub(γ , v) = γ
⟦ ts < t      ⟧Sub γ      = ⟦ ts ⟧Sub γ , ⟦ t ⟧Tm γ