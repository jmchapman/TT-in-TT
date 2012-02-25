module SyntacticLemmas where
open import Syntax

mutual
  fog⁺ : forall {Γ Γ'}{σ : Ty Γ}{σ' : Ty Γ'} -> σ ≡⁺ σ' -> Γ ≡Con Γ'
  fog⁺ (coh⁺ σ p) = symˠ p 
  fog⁺ refl⁺ = reflˠ 
  fog⁺ (trans⁺ p q) = transˠ (fog⁺ p) (fog⁺ q) 
  fog⁺ (sym⁺ p) = symˠ (fog⁺ p) 
  fog⁺ rightid⁺ = reflˠ 
  fog⁺ assoc⁺ = reflˠ
  fog⁺ (cong⁺ p q) = fogˢ q 
  fog⁺ (congU p) = p 
  fog⁺ (congEl p q) = p
  fog⁺ (congΠ p q) = fog⁺ p
  fog⁺ U[] = reflˠ
  fog⁺ El[] = reflˠ 
  fog⁺ Π[] = reflˠ
  fog⁺ (dom p) = fog⁺ p 
  fog⁺ (cod p) = cong, (fog⁺ p) (dom p)

  fog : forall {Γ Γ' σ σ'}{t : Tm Γ σ}{t' : Tm Γ' σ'} -> t ≡ t' ->
                σ ≡⁺ σ'
  fog (coh t p) = sym⁺ p
  fog refl = refl⁺
  fog (trans p q) = trans⁺ (fog p) (fog q)
  fog (sym p) = sym⁺ (fog p)
  fog rightid = rightid⁺
  fog assoc = assoc⁺
  fog (congtop p) = cong⁺ p (congpop p) 
  fog (cong p q) = cong⁺ (fog p) q
  fog (congλ p q) = congΠ p (fog q) 
  fog (congapp p) = cod (fog p) 
  fog β = refl⁺
  fog η = refl⁺
  fog top< = trans⁺ assoc⁺ (cong⁺ refl⁺ pop<)
  fog λ[] = refl⁺
  fog app[] = refl⁺ 

  fogˢ : forall {Γ Γ' Δ Δ'}{ts : Sub Γ Δ}{ts' : Sub Γ' Δ'} -> 
                   ts ≡ˢ ts' -> Γ ≡Con Γ'
  fogˢ (cohˢ ts p q) = symˠ p
  fogˢ reflˢ = reflˠ
  fogˢ (transˢ p q) = transˠ (fogˢ p) (fogˢ q)
  fogˢ (symˢ p) = symˠ (fogˢ p)
  fogˢ rightidˢ = reflˠ
  fogˢ assocˢ = reflˠ
  fogˢ (cong• p q) = fogˢ q
  fogˢ (congid p) = p
  fogˢ (congpop p) = cong, (fog⁺ p) p
  fogˢ (cong< p q) = fogˢ p
  fogˢ leftid = reflˠ
  fogˢ pop< = reflˠ
  fogˢ •< = reflˠ
  fogˢ poptop = reflˠ

εˢ : forall {Γ} -> Sub Γ ε
εˢ {ε}     = id
εˢ {Γ , σ} = εˢ • pop σ

ir : forall {Γ Γ' Γ'' Γ'''}{σ : Ty Γ}{σ' σ''}{σ''' : Ty Γ'''}
     {t : Tm Γ' σ'}{t' : Tm Γ'' σ''} -> 
     t ≡ t' -> {p : σ' ≡⁺ σ}{q : σ'' ≡⁺ σ'''} -> coe t p ≡ coe t' q
ir p =  trans (coh _ _) (trans p (sym (coh _ _)))


popid : forall {Γ Δ σ}{ts : Sub Γ Δ}{t : Tm Γ (σ [ ts ]⁺)} ->
        (ts • pop (σ [ ts ]⁺) < coe top assoc⁺) • (id < t [ id ]) ≡ˢ ts < t
popid = 
  transˢ •< (cong< (transˢ assocˢ (transˢ (cong• reflˢ pop<) rightidˢ))
                   (trans (coh _ _) (trans (trans (cong (coh _ _) reflˢ) top<) 
                                           rightid))) 

inst : forall {Γ Γ' Δ Δ' σ σ' τ τ'}{ts : Sub Γ Δ}{ts' : Sub Γ' Δ'}
      {t : Tm Γ (σ [ ts ]⁺)}{t' : Tm Γ' (σ' [ ts' ]⁺)} ->
      τ [ ts ↗ σ ]⁺ ≡⁺ τ' [ ts' ↗ σ' ]⁺ ->
      t ≡ t' -> τ [ ts < t ]⁺ ≡⁺ τ' [ ts' < t' ]⁺
inst p q = 
  trans⁺ (cong⁺ refl⁺ (symˢ popid))
         (trans⁺ (trans⁺ (sym⁺ assoc⁺) 
                         (trans⁺ (cong⁺ p 
                                        (cong< (congid (fog⁺ (fog q)))
                                               (trans rightid
                                                      (trans q 
                                                             (sym rightid)))))
                                 assoc⁺)) 
                 (cong⁺ refl⁺ popid))
