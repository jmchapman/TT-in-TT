module Syntax where

infix 10 _≡Con_
infix 10 _≡Ty_
infix 10 _≡ˢ_
infix 10 _≡Tm_
infixl 50 _•_

data Con : Set 
data _≡Con_ : Con -> Con -> Set 
data Ty : Con -> Set 
data Sub : Con -> Con -> Set 
data _≡Ty_ : forall {Γ Γ'} -> Ty Γ -> Ty Γ' -> Set 
data _≡ˢ_ : forall {Γ Γ' Δ Δ'} -> Sub Γ Δ -> Sub Γ' Δ' -> Set
data Tm : forall Γ -> Ty Γ -> Set 
data _≡Tm_ : forall {Γ Γ' σ σ'} -> Tm Γ σ -> Tm Γ' σ' -> Set 

data Con where
  ε   : Con
  _,_ : forall Γ -> Ty Γ -> Con

sub⁺ : forall {Γ σ} -> Ty (Γ , σ) -> Tm Γ σ -> Ty Γ

data _≡Con_ where
  congε : ε ≡Con ε
  cong, : forall {Γ Γ' σ σ'} -> Γ ≡Con Γ' -> σ ≡Ty σ' -> (Γ , σ) ≡Con (Γ' , σ')

data Ty  where
  coe⁺  : forall {Γ Δ} -> Ty Γ -> Γ ≡Con Δ -> Ty Δ
  _[_]⁺ : forall {Γ Δ} -> Ty Δ -> Sub Γ Δ -> Ty Γ
  U     : forall {Γ} -> Ty Γ
  El    : forall {Γ} -> Tm Γ U -> Ty Γ
  Π     : forall {Γ} σ -> Ty (Γ , σ) -> Ty Γ

_↗_ : forall {Γ Δ}(ts : Sub Γ Δ)(σ : Ty Δ) -> Sub (Γ , σ [ ts ]⁺) (Δ , σ)
Els : forall {Γ σ}{t : Tm Γ σ} -> Tm Γ (sub⁺ U t) -> Ty Γ
Elˢ : forall {Γ Δ}{ts : Sub Γ Δ} -> Tm Γ (U [ ts ]⁺) -> Ty Γ

data Sub where
  coeˢ : forall {Γ Γ' Δ Δ'} -> Sub Γ Δ -> Γ ≡Con Γ' -> Δ ≡Con Δ' -> 
         Sub Γ' Δ'
  _•_  : forall {B Γ Δ} -> Sub Γ Δ -> Sub B Γ -> Sub B Δ
  iden   : forall {Γ} -> Sub Γ Γ
  pop  : forall {Γ} σ -> Sub (Γ , σ) Γ
  _<_ : forall {Γ Δ σ}(ts : Sub Γ Δ) -> Tm Γ (σ [ ts ]⁺) -> 
        Sub Γ (Δ , σ)

_⇒_ : forall {Γ} -> Ty Γ -> Ty Γ -> Ty Γ
σ ⇒ τ = Π σ (τ [ pop σ ]⁺)

data Tm where
  coe  : forall {Γ Γ' σ σ'}-> Tm Γ σ -> σ ≡Ty σ' -> Tm Γ' σ'
  _[_] : forall {Γ Δ σ} -> Tm Δ σ -> (ts : Sub Γ Δ) -> Tm Γ (σ [ ts ]⁺)
  top  : forall {Γ σ} -> Tm (Γ , σ) (σ [ pop σ ]⁺)
  λt   : forall {Γ σ τ} -> Tm (Γ , σ) τ -> Tm Γ (Π σ τ)
  app  : forall {Γ σ τ} -> Tm Γ (Π σ τ) -> Tm (Γ , σ) τ


data _≡Ty_ where
  -- Setoid boilerplate
  coh⁺  : forall {Γ}{Δ}(σ : Ty Γ)(p : Γ ≡Con Δ) -> coe⁺ σ p ≡Ty σ

  -- Equivalence boilerplate
  refl⁺ : forall {Γ}{σ : Ty Γ} -> σ ≡Ty σ
  trans⁺ : forall {Γ}{Γ'}{Γ''}{σ : Ty Γ}{σ' : Ty Γ'}{σ'' : Ty Γ''} -> 
           σ ≡Ty σ' -> σ' ≡Ty σ'' -> σ ≡Ty σ''
  sym⁺ : forall {Γ}{Γ'}{σ : Ty Γ}{σ' : Ty Γ'} -> σ ≡Ty σ' -> σ' ≡Ty σ
  
  -- Substitution boilerplate
  rightid⁺ : forall {Γ}{σ : Ty Γ} -> σ [ iden ]⁺ ≡Ty σ
  assoc⁺ : forall {B}{Γ}{Δ}{σ}{ts : Sub Γ Δ}{us : Sub B Γ} -> 
          σ [ ts ]⁺ [ us ]⁺  ≡Ty σ [ ts • us ]⁺
  cong⁺ : forall {Γ Γ'}{Δ Δ'}{σ}{σ'}{ts : Sub Γ Δ}{ts' : Sub Γ' Δ'} -> 
         σ ≡Ty σ' -> ts ≡ˢ ts' ->
         σ [ ts ]⁺ ≡Ty σ' [ ts' ]⁺

  -- Congruence boilerplate
  congU : forall {Γ}{Γ'} -> Γ ≡Con Γ' -> U {Γ} ≡Ty U {Γ'}
  congEl : forall {Γ Γ'}{t : Tm Γ U}{t' : Tm Γ' U} -> Γ ≡Con Γ' -> t ≡Tm t' -> 
           El t ≡Ty El t'
  congΠ : forall {Γ}{σ : Ty Γ}{τ : Ty (Γ , σ)} -> 
       forall {Γ'}{σ' : Ty Γ'}{τ' : Ty (Γ' , σ')} -> 
       (p : σ ≡Ty σ')(q : τ ≡Ty τ') ->
       Π σ τ ≡Ty Π σ' τ'

  -- Computation rules
  U[] : forall {Γ}{Δ}{ts : Sub Γ Δ} -> U [ ts ]⁺ ≡Ty U {Γ}
  El[] : forall {Γ}{Δ}{t : Tm Δ U}{ts : Sub Γ Δ} -> 
         El t [ ts ]⁺ ≡Ty Elˢ (t [ ts ])
  Π[] : forall {Γ}{Δ}{σ}{τ}{ts : Sub Γ Δ} -> 
        Π σ τ [ ts ]⁺ ≡Ty Π (σ [ ts ]⁺) (τ [ ts ↗  σ ]⁺)

  -- equality projections
--  dom : forall {Γ Γ' σ σ'}{τ : Ty (Γ , σ)}{τ' : Ty (Γ' , σ')} ->
--        Π σ τ ≡Ty Π σ' τ' -> σ ≡Ty σ'
--  cod : forall {Γ Γ' σ σ'}{τ : Ty (Γ , σ)}{τ' : Ty (Γ' , σ')} -> Π σ τ ≡Ty Π σ' τ' -> τ ≡Ty τ'

data _≡ˢ_ where
  -- Setoid boilerplate
  cohˢ : forall {Γ Γ' Δ Δ'}(ts : Sub Γ Δ)(p : Γ ≡Con Γ')(q : Δ ≡Con Δ') ->
          coeˢ ts p q  ≡ˢ ts

  -- Equivalence boilerplate
  reflˢ : forall {Γ}{Δ}{ts : Sub Γ Δ} -> ts ≡ˢ ts
  transˢ : forall {Γ Γ' Γ''}{Δ Δ' Δ''} -> 
           {ts : Sub Γ Δ}{ts' : Sub Γ' Δ'}{ts'' : Sub Γ'' Δ''} -> 
           ts ≡ˢ ts' -> ts' ≡ˢ ts'' -> ts ≡ˢ ts''
  symˢ : forall {Γ Γ'}{Δ Δ'}{ts : Sub Γ Δ}{ts' : Sub Γ' Δ'} ->
         ts ≡ˢ ts' -> ts' ≡ˢ ts

  -- Subsitution boilerplate
  rightidˢ : forall {Γ}{Δ}{ts : Sub Γ Δ} -> (ts • iden) ≡ˢ ts
  assocˢ : forall {A}{B}{Γ}{Δ}{ts : Sub Γ Δ}{us : Sub B Γ}{vs : Sub A B} ->
       (ts • us • vs) ≡ˢ ts • (us • vs)

  -- Congruence boilerplate
  cong• : forall {B B' Γ Γ' Δ Δ'}{ts : Sub Γ Δ}{us : Sub B Γ} ->
          {ts' : Sub Γ' Δ'}{us' : Sub B' Γ'} -> ts ≡ˢ ts' -> us ≡ˢ us' ->
          ts • us ≡ˢ ts' • us'
  congid : forall {Γ Γ'} -> Γ ≡Con Γ' -> iden {Γ} ≡ˢ iden {Γ'}
  congpop : forall {Γ Γ'}{σ : Ty Γ}{σ' : Ty Γ'} -> 
       σ ≡Ty σ' ->  pop σ ≡ˢ pop σ'
  cong< : forall {Γ Γ'}{Δ Δ'}{σ}{σ'}{ts : Sub Γ Δ}{ts' : Sub Γ' Δ'}
        {t : Tm Γ (σ [ ts ]⁺)}{t' : Tm Γ' (σ' [ ts' ]⁺)} -> 
        ts ≡ˢ ts' -> t ≡Tm t' -> (ts < t) ≡ˢ (ts' < t')

  -- Computation rules
  leftid : forall {Γ}{Δ}{ts : Sub Γ Δ} -> (iden • ts) ≡ˢ ts
  pop< : forall {Γ}{Δ}{σ}{ts : Sub Γ Δ}{t : Tm Γ (σ [ ts ]⁺)} -> 
         (pop σ • (ts < t)) ≡ˢ ts
  •< : forall {B}{Γ}{Δ}{σ} -> 
       {ts : Sub Γ Δ}{t : Tm Γ (σ [ ts ]⁺)}{us : Sub B Γ} -> 
       (ts < t) • us ≡ˢ (ts • us < coe (t [ us ]) assoc⁺)
  poptop : forall {Γ}{σ} -> (pop σ < top) ≡ˢ iden {Γ , σ}

-- smart constructors
sub⁺ σ t = σ [ iden < t [ iden ] ]⁺ 

Elˢ σ = El (coe σ U[])  


Els σ = El (coe σ U[]) 

sub : forall {Γ σ τ} -> Tm (Γ , σ) τ -> (a : Tm Γ σ) -> Tm Γ (sub⁺ τ a)
sub u t = u [ iden < t [ iden ] ] 

_$_ : forall {Γ σ τ} -> Tm Γ (Π σ τ) -> (a : Tm Γ σ) -> Tm Γ (sub⁺ τ a)
f $ a = sub (app f) a  

ts ↗ σ = ts • pop _ < coe top assoc⁺ 

_↑_ : forall {Γ Δ}(ts : Sub Γ Δ)(σ : Tm Δ U) -> 
      Sub (Γ , Elˢ (σ [ ts ])) (Δ , El σ)
ts ↑ σ = ts • pop _ < coe top (trans⁺ (cong⁺ (sym⁺ El[]) reflˢ) assoc⁺)

data _≡Tm_  where
  -- Setoid boilerplate
  coh  : forall {Γ}{Γ'}{σ : Ty Γ}{σ' : Ty Γ'}(t : Tm Γ σ)(p : σ ≡Ty σ') ->
         coe t p ≡Tm t

  -- Equivalence boilerplate
  refl : forall {Γ}{σ}{t : Tm Γ σ} -> t ≡Tm t
  sym : forall {Γ}{Γ'}{σ}{σ'}{t : Tm Γ σ}{t' : Tm Γ' σ'} -> 
        t ≡Tm t' -> t' ≡Tm t
  trans : forall {Γ Γ' Γ''}{σ}{σ'}{σ''} ->
         {t : Tm Γ σ}{t' : Tm Γ' σ'}{t'' : Tm Γ'' σ''} -> 
         t ≡Tm t' -> t' ≡Tm t'' -> t ≡Tm t''

  -- Substitution boilerplate
  rightid : forall {Γ}{σ : Ty Γ}{t : Tm Γ σ} -> t [ iden ] ≡Tm t
  assoc : forall {B}{Γ}{Δ}{σ}{t : Tm Δ σ}{ts : Sub Γ Δ}{us : Sub B Γ} -> 
          t [ ts ] [ us ]  ≡Tm  t [ ts • us ]
  cong : forall {Γ Γ'}{Δ Δ'}{σ : Ty Δ}{σ' : Ty Δ'} ->
        {t : Tm Δ σ}{t' : Tm Δ' σ'}{ts : Sub Γ Δ}{ts' : Sub Γ' Δ'} ->
        t ≡Tm t' -> ts ≡ˢ ts' ->
        t [ ts ] ≡Tm t' [ ts' ]

  -- Congruence boilerplate
  congtop : forall {Γ Γ'}{σ : Ty Γ}{σ' : Ty Γ'} -> σ ≡Ty σ' -> 
            top {σ = σ} ≡Tm top {σ = σ'}
  congλ : forall {Γ Γ' σ σ' τ τ'}
       {t : Tm (Γ , σ) τ}{t' : Tm (Γ' , σ') τ'} -> σ ≡Ty σ' ->
       t ≡Tm t' -> λt t ≡Tm λt t'
  congapp : forall {Γ Γ' σ σ' τ τ'} -> 
       {t : Tm Γ (Π σ τ)}{t' : Tm Γ' (Π σ' τ')} -> τ ≡Ty τ' → t ≡Tm t' -> app t ≡Tm app t'

  -- computation rules
  η : forall {Γ σ τ}{f : Tm Γ (Π σ τ)} -> 
        λt (app f) ≡Tm f
  β : forall {Γ σ τ}{t : Tm (Γ , σ) τ} ->
      app (λt t) ≡Tm t
  top< : forall {Γ Δ σ}{ts : Sub Γ Δ}{t : Tm Γ (σ [ ts ]⁺)} ->
         top [ ts < t ] ≡Tm t
  λ[] : forall {Γ Δ σ τ}{t : Tm (Δ , σ) τ}{ts : Sub Γ Δ} ->
        coe (λt t [ ts ]) Π[] ≡Tm λt (t [ ts ↗ σ ])
  app[] : forall {Γ Δ σ τ}{f : Tm Δ (Π σ τ)}{ts : Sub Γ Δ} ->
         app (coe (f [ ts ]) Π[]) ≡Tm app f [ ts ↗  σ ]


reflˠ : forall {Γ} -> Γ ≡Con Γ
reflˠ {ε} = congε 
reflˠ {Γ , σ} = cong, (reflˠ {Γ}) refl⁺

symˠ : forall {Γ Γ'} -> Γ ≡Con Γ' -> Γ' ≡Con Γ
symˠ congε  = congε 
symˠ (cong, p q)  = cong, (symˠ p) (sym⁺ q) 

transˠ : forall {Γ Γ' Γ''} -> Γ ≡Con Γ' -> Γ' ≡Con Γ'' -> Γ ≡Con Γ''
transˠ congε congε = congε 
transˠ (cong, p q) (cong, p' q') = cong, (transˠ p p') (trans⁺ q q') 

_$ˢ_ : forall {Γ Δ σ τ}{ts : Sub Γ Δ} -> 
       Tm Γ (Π σ τ [ ts ]⁺) ->
       (a : Tm Γ (σ [ ts ]⁺)) ->
       Tm Γ (τ [ ts < a ]⁺)
f $ˢ a = 
  coe 
    (coe f Π[] $ a) 
    (trans⁺ 
       (trans⁺ 
          assoc⁺ 
          (trans⁺ 
             (cong⁺ 
                refl⁺ 
                (transˢ 
                   (transˢ 
                      •< 
                      (cong< 
                         (transˢ assocˢ (cong• reflˢ pop<))
                         (trans 
                            (coh _ _) 
                            (trans 
                               (trans (cong (coh _ _) reflˢ) top<)
                               (sym (coh _ _))))))
                   (symˢ •<)))
             (sym⁺ assoc⁺)))
       rightid⁺)
