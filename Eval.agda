
module Eval (A : Set)(B : A → Set) where

open import Data.Unit
open import Data.Product
open import Function
open import Relation.Binary.HeterogeneousEquality hiding (Extensionality)

open import Syntax renaming (sym to symT;trans to transT; refl to reflT; cong to congT)
open import SyntacticLemmas

Extensionality : ∀ a b → Set _
Extensionality a b =
  {A A' : Set a} {B₁ : A → Set b}{B₂ : A' → Set b}
  {f₁ : (x : A) → B₁ x} {f₂ : (x : A') → B₂ x} →
  (∀ {x x'} → x ≅ x' → f₁ x ≅ f₂ x') → f₁ ≅ f₂
postulate ext : ∀{a b} → Extensionality a b

eq-lem : ∀{l}{A A' : Set l} → {a : A} → {a' : A'} → a ≅ a' → A ≅ A'
eq-lem refl = refl


Σ-eq : ∀{a b} {A A' : Set a} → {B : A → Set b} → {B' : A' → Set b} → B ≅ B' → {p : Σ A B} → {p' : Σ A' B'} → proj₁ p ≅ proj₁ p' → 
       proj₂ p ≅ proj₂ p' → p ≅ p'
Σ-eq p' p q with eq-lem p
Σ-eq {A' = A'}{B' = B'} refl p q | refl = cong₂ {A = A'}{B = B'}{C = λ _ _ → Σ A' B'} _,_ p q


Σ-eqfst : {A A' : Set} → A ≅ A' → {B : A → Set} → {B' : A' → Set} → B ≅ B' → {p : Σ A B} → {p' : Σ A' B'} → p ≅ p' → 
          proj₁ p ≅ proj₁ p'
Σ-eqfst refl refl refl = refl

Σ-eqsnd : {A A' : Set} → A ≅ A' → {B : A → Set} → {B' : A' → Set} → B ≅ B' → {p : Σ A B} → {p' : Σ A' B'} → p ≅ p' → 
          proj₂ p ≅ proj₂ p'
Σ-eqsnd refl refl refl = refl


⟦_⟧Con : Con → Set
⟦_⟧Ty  : ∀{Γ} → Ty Γ → ⟦ Γ ⟧Con → Set
⟦_⟧Tm  : ∀{Γ σ} → Tm Γ σ → (γ : ⟦ Γ ⟧Con) → ⟦ σ ⟧Ty γ
⟦_⟧Sub : ∀{Γ Δ} → Sub Γ Δ → ⟦ Γ ⟧Con → ⟦ Δ ⟧Con


⟦_⟧Con≡ : ∀{Γ Γ' : Con} → Γ ≡Con Γ' → ⟦ Γ ⟧Con ≅ ⟦ Γ' ⟧Con

⟦_⟧Ty≡  : ∀{Γ Γ'}{σ : Ty Γ}{σ' : Ty Γ'}{γ : ⟦ Γ ⟧Con}{γ' : ⟦ Γ' ⟧Con}(p : σ ≡Ty σ')(q : γ ≅ γ') → ⟦ σ ⟧Ty γ ≅ ⟦ σ' ⟧Ty γ'

⟦_⟧Sub≡_ : ∀{Γ Γ' Δ Δ'}{ts : Sub Γ Δ}{ts' : Sub Γ' Δ'}{γ : ⟦ Γ ⟧Con}{γ' : ⟦ Γ' ⟧Con}
           (p : ts ≡ˢ ts')(q : γ ≅ γ')  → ⟦ ts ⟧Sub γ ≅ ⟦ ts' ⟧Sub γ'

⟦ ε     ⟧Con = ⊤
⟦ Γ , σ ⟧Con = Σ ⟦ Γ ⟧Con ⟦ σ ⟧Ty 

⟦_⟧U : ∀{Γ} → Tm Γ U → ⟦ Γ ⟧Con  → A

⟦ coe⁺ σ p  ⟧Ty γ = ⟦ σ ⟧Ty (subst (λ x → x) (sym ⟦ p ⟧Con≡) γ )
⟦ σ [ ts ]⁺ ⟧Ty γ = ⟦ σ ⟧Ty (⟦ ts ⟧Sub γ)
⟦ U         ⟧Ty γ = A
⟦ El σ      ⟧Ty γ = B (⟦ σ ⟧U γ) 
⟦ Π σ  τ    ⟧Ty γ = (x : ⟦ σ ⟧Ty γ) → ⟦ τ ⟧Ty (γ , x) 

⟦ coe t p ⟧Tm γ        = subst id  
                               (⟦ p ⟧Ty≡ (subst-removable id (sym ⟦ fog⁺ p ⟧Con≡) γ)) 
                               (⟦ t ⟧Tm (subst id (sym ⟦ fog⁺ p ⟧Con≡) γ ))
⟦ t [ ts ] ⟧Tm γ       = ⟦ t ⟧Tm (⟦ ts ⟧Sub γ)
⟦ top      ⟧Tm (γ , v) = {!!} -- v
⟦ λt t     ⟧Tm γ       = λ v → ⟦ t ⟧Tm (γ , v)
⟦ app t    ⟧Tm (γ , v) = ⟦ t ⟧Tm γ v 

⟦ coeˢ ts p q ⟧Sub γ      = subst id ⟦ q ⟧Con≡ (⟦ ts ⟧Sub (subst id (sym ⟦ p ⟧Con≡) γ))
⟦ ts • ts'    ⟧Sub γ      = ⟦ ts ⟧Sub (⟦ ts' ⟧Sub γ)
⟦ iden        ⟧Sub γ      = γ
⟦ pop σ       ⟧Sub(γ , v) = γ
⟦ ts < t      ⟧Sub γ      = ⟦ ts ⟧Sub γ , ⟦ t ⟧Tm γ

⟦ congε     ⟧Con≡ = refl
⟦ cong, p q ⟧Con≡ = cong₂ Σ ⟦ p ⟧Con≡  (ext ⟦ q ⟧Ty≡)

⟦ coh⁺ σ' p ⟧Ty≡ q = cong ⟦ σ' ⟧Ty (trans (subst-removable id (sym ⟦ p ⟧Con≡) _) q)
⟦_⟧Ty≡ refl⁺ refl = refl
⟦_⟧Ty≡ {γ = γ} (trans⁺ p q) r = {!⟦ !}
⟦ sym⁺ p     ⟧Ty≡ q = sym (⟦ p ⟧Ty≡ (sym q))
⟦_⟧Ty≡  {σ' = σ'} rightid⁺ p = {!!} -- cong ⟦ σ' ⟧Ty p
⟦ assoc⁺ {σ = σ}{ts = ts}{us = us} ⟧Ty≡  p = cong (λ γ → ⟦ σ ⟧Ty (⟦ ts ⟧Sub (⟦ us ⟧Sub γ))) p
⟦ cong⁺ p q  ⟧Ty≡ r = ⟦ p ⟧Ty≡  (⟦ q ⟧Sub≡ r) 
⟦ congU p    ⟧Ty≡ q = refl
⟦ congEl p q ⟧Ty≡ r = {!!}
⟦ congΠ p q  ⟧Ty≡ r = cong₂ (λ X (Y : X → _) → (x : X) → Y x) (⟦ p ⟧Ty≡ r) (ext (λ x0 → ⟦ q ⟧Ty≡ (Σ-eq (ext ⟦ p ⟧Ty≡) r x0))) 
⟦ U[]        ⟧Ty≡ p = refl
⟦ El[] {t = t}{ts = ts} ⟧Ty≡  refl = {!!} 
  -- cong (λ γ → B (⟦ t ⟧U (⟦ ts ⟧Sub γ))) (sym (subst-removable id (sym ⟦ reflˠ ⟧Con≡) _))
⟦_⟧Ty≡ {γ = γ}{γ' = γ'}(Π[] {σ = σ}{τ = τ}{ts = ts}) p = {!!}

⟦_⟧Sub≡_  = {!!}

⟦ u ⟧U = ⟦ u ⟧Tm
