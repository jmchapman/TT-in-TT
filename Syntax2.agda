module Syntax2 where

infix 10 _≡ˠ_
infix 10 _≡⁺_
infix 10 _≡ˢ_
infix 10 _≡_
infixl 50 _•_

mutual 
  data Con : Set where
    ε   : Con
    _,_ : forall Γ -> Ty Γ -> Con

  data _≡ˠ_ : Con -> Con -> Set where
    congε : ε ≡ˠ ε
    cong, : forall {Γ Γ' σ σ'} -> Γ ≡ˠ Γ' -> σ ≡⁺ σ' -> (Γ , σ) ≡ˠ (Γ' , σ')

  data Ty : Con -> Set where
    coe⁺  : forall {Γ Δ} -> Ty Γ -> Γ ≡ˠ Δ -> Ty Δ
    _[_]⁺ : forall {Γ Δ} -> Ty Δ -> Sub Γ Δ -> Ty Γ
    U     : forall {Γ} -> Ty Γ
    El    : forall {Γ} -> Tm Γ U -> Ty Γ
    Π     : forall {Γ} σ -> Ty (Γ , σ) -> Ty Γ

  _,'_ : forall Γ -> Ty Γ -> Con
  _,'_ = _,_
  Π' : forall {Γ} σ -> Ty (Γ ,' σ) -> Ty Γ
  Π' = Π
  U' : forall {Γ} -> Ty Γ
  U' = U

  data Sub : Con -> Con -> Set where
    coeˢ : forall {Γ Γ' Δ Δ'} -> Sub Γ Δ -> Γ ≡ˠ Γ' -> Δ ≡ˠ Δ' -> 
           Sub Γ' Δ'
    _•_  : forall {B Γ Δ} -> Sub Γ Δ -> Sub B Γ -> Sub B Δ
    id   : forall {Γ} -> Sub Γ Γ
    pop  : forall {Γ} σ -> Sub (Γ , σ) Γ
    _<_ : forall {Γ Δ σ}(ts : Sub Γ Δ) -> Tm Γ (σ [ ts ]⁺) -> 
          Sub Γ (Δ , σ)

  _⇒_ : forall {Γ} -> Ty Γ -> Ty Γ -> Ty Γ
  σ ⇒ τ = Π σ (τ [ pop σ ]⁺)

  _•'_ : forall {B Γ Δ} -> Sub Γ Δ -> Sub B Γ -> Sub B Δ
  _•'_ = _•_
  id' : forall {Γ} -> Sub Γ Γ
  id' = id
  _[_]⁺' : forall {Γ Δ} -> Ty Δ -> Sub Γ Δ -> Ty Γ
  _[_]⁺' = _[_]⁺
  pop'  : forall {Γ} σ -> Sub (Γ ,' σ) Γ
  pop' = pop

  data _≡⁺_ : forall {Γ Γ'} -> Ty Γ -> Ty Γ' -> Set where
    -- Setoid boilerplate
    coh⁺  : forall {Γ}{Δ}(σ : Ty Γ)(p : Γ ≡ˠ Δ) -> coe⁺ σ p ≡⁺ σ

    -- Equivalence boilerplate
    refl⁺ : forall {Γ}{σ : Ty Γ} -> σ ≡⁺ σ
    trans⁺ : forall {Γ}{Γ'}{Γ''}{σ : Ty Γ}{σ' : Ty Γ'}{σ'' : Ty Γ''} -> 
             σ ≡⁺ σ' -> σ' ≡⁺ σ'' -> σ ≡⁺ σ''
    sym⁺  : forall {Γ}{Γ'}{σ : Ty Γ}{σ' : Ty Γ'} -> σ ≡⁺ σ' -> σ' ≡⁺ σ
    
    -- Substitution boilerplate
    rightid⁺ : forall {Γ}{σ : Ty Γ} -> σ [ id' ]⁺ ≡⁺ σ
    assoc⁺ : forall {B}{Γ}{Δ}{σ}{ts : Sub Γ Δ}{us : Sub B Γ} -> 
            σ [ ts ]⁺ [ us ]⁺  ≡⁺ σ [ ts • us ]⁺
    cong⁺ : forall {Γ Γ'}{Δ Δ'}{σ}{σ'}{ts : Sub Γ Δ}{ts' : Sub Γ' Δ'} -> 
           σ ≡⁺ σ' -> ts ≡ˢ ts' ->
           σ [ ts ]⁺ ≡⁺ σ' [ ts' ]⁺

    -- Congruence boilerplate
    congU : forall {Γ}{Γ'} -> Γ ≡ˠ Γ' -> U {Γ} ≡⁺ U {Γ'}
    congEl : forall {Γ Γ'}{t : Tm Γ U}{t' : Tm Γ' U} -> Γ ≡ˠ Γ' -> t ≡ t' -> 
             El t ≡⁺ El t'
    congΠ : forall {Γ}{σ : Ty Γ}{τ : Ty (Γ , σ)} -> 
         forall {Γ'}{σ' : Ty Γ'}{τ' : Ty (Γ' , σ')} -> 
         (p : σ ≡⁺ σ')(q : τ ≡⁺ τ') ->
         Π σ τ ≡⁺ Π σ' τ'

    -- Computation rules
    U[] : forall {Γ}{Δ}{ts : Sub Γ Δ} -> U [ ts ]⁺ ≡⁺ U {Γ}
    El[] : forall {Γ}{Δ}{t : Tm Δ U}{ts : Sub Γ Δ} -> 
           El t [ ts ]⁺ ≡⁺ Elˢ (t [ ts ]')
    Π[] : forall {Γ}{Δ}{σ}{τ}{ts : Sub Γ Δ} -> 
          Π σ τ [ ts ]⁺ ≡⁺ Π (σ [ ts ]⁺) (τ [ ts ↗  σ ]⁺)

    -- equality projections
    dom : forall {Γ Γ' σ σ'}{τ : Ty (Γ , σ)}{τ' : Ty (Γ' , σ')} ->
          Π σ τ ≡⁺ Π σ' τ' -> σ ≡⁺ σ'
    cod : forall {Γ Γ' σ σ'}{τ : Ty (Γ , σ)}{τ' : Ty (Γ' , σ')} -> Π σ τ ≡⁺ Π σ' τ' -> τ ≡⁺ τ'

  data _≡ˢ_ : forall {Γ Γ' Δ Δ'} -> Sub Γ Δ -> Sub Γ' Δ' -> Set where
    -- Setoid boilerplate
    cohˢ : forall {Γ Γ' Δ Δ'}(ts : Sub Γ Δ)(p : Γ ≡ˠ Γ')(q : Δ ≡ˠ Δ') ->
            coeˢ ts p q  ≡ˢ ts

    -- Equivalence boilerplate
    reflˢ : forall {Γ}{Δ}{ts : Sub Γ Δ} -> ts ≡ˢ ts
    transˢ : forall {Γ Γ' Γ''}{Δ Δ' Δ''} -> 
             {ts : Sub Γ Δ}{ts' : Sub Γ' Δ'}{ts'' : Sub Γ'' Δ''} -> 
             ts ≡ˢ ts' -> ts' ≡ˢ ts'' -> ts ≡ˢ ts''
    symˢ : forall {Γ Γ'}{Δ Δ'}{ts : Sub Γ Δ}{ts' : Sub Γ' Δ'} ->
           ts ≡ˢ ts' -> ts' ≡ˢ ts

    -- Subsitution boilerplate
    rightidˢ : forall {Γ}{Δ}{ts : Sub Γ Δ} -> (ts • id) ≡ˢ ts
    assocˢ : forall {A}{B}{Γ}{Δ}{ts : Sub Γ Δ}{us : Sub B Γ}{vs : Sub A B} ->
         (ts • us • vs) ≡ˢ ts • (us • vs)

    -- Congruence boilerplate
    cong• : forall {B B' Γ Γ' Δ Δ'}{ts : Sub Γ Δ}{us : Sub B Γ} ->
            {ts' : Sub Γ' Δ'}{us' : Sub B' Γ'} -> ts ≡ˢ ts' -> us ≡ˢ us' ->
            ts • us ≡ˢ ts' • us'
    congid : forall {Γ Γ'} -> Γ ≡ˠ Γ' -> id {Γ} ≡ˢ id {Γ'}
    congpop : forall {Γ Γ'}{σ : Ty Γ}{σ' : Ty Γ'} -> 
         σ ≡⁺ σ' ->  pop σ ≡ˢ pop σ'
    cong< : forall {Γ Γ'}{Δ Δ'}{σ}{σ'}{ts : Sub Γ Δ}{ts' : Sub Γ' Δ'}
          {t : Tm Γ (σ [ ts ]⁺)}{t' : Tm Γ' (σ' [ ts' ]⁺)} -> 
          ts ≡ˢ ts' -> t ≡ t' -> (ts < t) ≡ˢ (ts' < t')

    -- Computation rules
    leftid : forall {Γ}{Δ}{ts : Sub Γ Δ} -> (id • ts) ≡ˢ ts
    pop< : forall {Γ}{Δ}{σ}{ts : Sub Γ Δ}{t : Tm Γ (σ [ ts ]⁺)} -> 
           (pop σ • (ts < t)) ≡ˢ ts
    •< : forall {B}{Γ}{Δ}{σ} -> 
         {ts : Sub Γ Δ}{t : Tm Γ (σ [ ts ]⁺)}{us : Sub B Γ} -> 
         (ts < t) • us ≡ˢ (ts • us < coe' (t [ us ]') assoc⁺)
    poptop : forall {Γ}{σ} -> (pop σ < top') ≡ˢ id {Γ , σ}

  data Tm : forall Γ -> Ty Γ -> Set where
    coe  : forall {Γ Γ' σ σ'}-> Tm Γ σ -> σ ≡⁺ σ' -> Tm Γ' σ'
    _[_] : forall {Γ Δ σ} -> Tm Δ σ -> (ts : Sub Γ Δ) -> Tm Γ (σ [ ts ]⁺)
    top  : forall {Γ σ} -> Tm (Γ , σ) (σ [ pop σ ]⁺)
    λt   : forall {Γ σ τ} -> Tm (Γ , σ) τ -> Tm Γ (Π σ τ)
    app  : forall {Γ σ τ} -> Tm Γ (Π σ τ) -> Tm (Γ , σ) τ

  El' : forall {Γ} -> Tm Γ U' -> Ty Γ
  El' = El
  _[_]' : forall {Γ Δ σ} -> Tm Δ σ -> (ts : Sub Γ Δ) -> Tm Γ (σ [ ts ]⁺')
  _[_]' = _[_]
  _<'_ : forall {Γ Δ σ}(ts : Sub Γ Δ) -> Tm Γ (σ [ ts ]⁺') -> 
        Sub Γ (Δ ,' σ)
  _<'_ = _<_
  top' : forall {Γ σ} -> Tm (Γ ,' σ) (σ [ pop' σ ]⁺')
  top' = top  
  coe' : forall {Γ Γ' σ σ'}-> Tm Γ σ -> σ ≡⁺ σ' -> Tm Γ' σ'
  coe' = coe

  -- smart constructors
  sub⁺ : forall {Γ σ} -> Ty (Γ ,' σ) -> Tm Γ σ -> Ty Γ
  sub⁺ σ t = σ [ id < t [ id ]' ]⁺ 

  Elˢ : forall {Γ Δ}{ts : Sub Γ Δ} -> Tm Γ (U' [ ts ]⁺') -> Ty Γ
  Elˢ σ = El (coe σ U[])  

  Els : forall {Γ σ}{t : Tm Γ σ} -> Tm Γ (sub⁺ U' t) -> Ty Γ
  Els σ = El (coe σ U[]) 

  sub : forall {Γ σ τ} -> Tm (Γ ,' σ) τ -> (a : Tm Γ σ) -> Tm Γ (sub⁺ τ a)
  sub u t = u [ id < t [ id ] ] 

  _$_ : forall {Γ σ τ} -> Tm Γ (Π' σ τ) -> (a : Tm Γ σ) -> Tm Γ (sub⁺ τ a)
  f $ a = sub (app f) a  

  _↗_ : forall {Γ Δ}(ts : Sub Γ Δ)(σ : Ty Δ) -> Sub (Γ ,' σ [ ts ]⁺') (Δ ,' σ)
  ts ↗ σ = ts • pop _ < coe top assoc⁺ 

  _↑_ : forall {Γ Δ}(ts : Sub Γ Δ)(σ : Tm Δ U') -> 
        Sub (Γ ,' Elˢ (σ [ ts ]')) (Δ ,' El' σ)
  ts ↑ σ = ts • pop _ < coe top (trans⁺ (cong⁺ (sym⁺ El[]) reflˢ) assoc⁺)

  data _≡_ : forall {Γ Γ' σ σ'} -> Tm Γ σ -> Tm Γ' σ' -> Set where
    -- Setoid boilerplate
    coh  : forall {Γ}{Γ'}{σ : Ty Γ}{σ' : Ty Γ'}(t : Tm Γ σ)(p : σ ≡⁺ σ') ->
           coe t p ≡ t

    -- Equivalence boilerplate
    refl : forall {Γ}{σ}{t : Tm Γ σ} -> t ≡ t
    sym : forall {Γ}{Γ'}{σ}{σ'}{t : Tm Γ σ}{t' : Tm Γ' σ'} -> 
          t ≡ t' -> t' ≡ t
    trans : forall {Γ Γ' Γ''}{σ}{σ'}{σ''} ->
           {t : Tm Γ σ}{t' : Tm Γ' σ'}{t'' : Tm Γ'' σ''} -> 
           t ≡ t' -> t' ≡ t'' -> t ≡ t''

    -- Substitution boilerplate
    rightid : forall {Γ}{σ : Ty Γ}{t : Tm Γ σ} -> t [ id ] ≡ t
    assoc : forall {B}{Γ}{Δ}{σ}{t : Tm Δ σ}{ts : Sub Γ Δ}{us : Sub B Γ} -> 
            t [ ts ] [ us ]  ≡  t [ ts • us ]
    cong : forall {Γ Γ'}{Δ Δ'}{σ : Ty Δ}{σ' : Ty Δ'} ->
          {t : Tm Δ σ}{t' : Tm Δ' σ'}{ts : Sub Γ Δ}{ts' : Sub Γ' Δ'} ->
          t ≡ t' -> ts ≡ˢ ts' ->
          t [ ts ] ≡ t' [ ts' ]

    -- Congruence boilerplate
    congtop : forall {Γ Γ'}{σ : Ty Γ}{σ' : Ty Γ'} -> σ ≡⁺ σ' -> 
              top {σ = σ} ≡ top {σ = σ'}
    congλ : forall {Γ Γ' σ σ' τ τ'}
         {t : Tm (Γ , σ) τ}{t' : Tm (Γ' , σ') τ'} -> σ ≡⁺ σ' ->
         t ≡ t' -> λt t ≡ λt t'
    congapp : forall {Γ Γ' σ σ' τ τ'} -> 
         {t : Tm Γ (Π σ τ)}{t' : Tm Γ' (Π σ' τ')} -> t ≡ t' -> app t ≡ app t'

    -- computation rules
--    η : forall {Γ σ τ}{f : Tm Γ (Π σ τ)} -> 
--        λ (app f) ≡ f
    β : forall {Γ σ τ}{t : Tm (Γ , σ) τ} ->
        app (λt t) ≡ t
    top< : forall {Γ Δ σ}{ts : Sub Γ Δ}{t : Tm Γ (σ [ ts ]⁺)} ->
           top [ ts < t ] ≡ t
    λ[] : forall {Γ Δ σ τ}{t : Tm (Δ , σ) τ}{ts : Sub Γ Δ} ->
          coe (λt t [ ts ]) Π[] ≡ λt (t [ ts ↗ σ ])
    app[] : forall {Γ Δ σ τ}{f : Tm Δ (Π σ τ)}{ts : Sub Γ Δ} ->
           app (coe (f [ ts ]) Π[]) ≡ app f [ ts ↗  σ ]


  reflˠ : forall {Γ} -> Γ ≡ˠ Γ
  reflˠ {ε} = congε 
  reflˠ {Γ , σ} = cong, (reflˠ {Γ}) refl⁺

  symˠ : forall {Γ Γ'} -> Γ ≡ˠ Γ' -> Γ' ≡ˠ Γ
  symˠ congε  = congε 
  symˠ (cong, p q)  = cong, (symˠ p) (sym⁺ q) 

  transˠ : forall {Γ Γ' Γ''} -> Γ ≡ˠ Γ' -> Γ' ≡ˠ Γ'' -> Γ ≡ˠ Γ''
  transˠ congε congε = congε 
  transˠ (cong, p q) (cong, p' q') = cong, (transˠ p p') (trans⁺ q q') 

  _$ˢ_ : forall {Γ Δ σ τ}{ts : Sub Γ Δ} -> 
         Tm Γ (Π' σ τ [ ts ]⁺') ->
         (a : Tm Γ (σ [ ts ]⁺')) ->
         Tm Γ (τ [ ts <' a ]⁺')
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
