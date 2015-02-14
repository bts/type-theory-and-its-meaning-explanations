{-# OPTIONS --type-in-type #-}

open import Agda.Primitive

postulate Ident : Set
{-# BUILTIN STRING Ident #-}

record Σ (A : Set) (B : A → Set) : Set where
  constructor ⟨_,_⟩
  field
    fst : A
    snd : B fst

[_] : ∀ {A B} (M : A) {{N : B M}} → Σ A B
[_] M {{N}} = ⟨ M , N ⟩

data Bool : Set where
  tt ff : Bool

data ℕ : Set where
  ze : ℕ
  su : ℕ → ℕ
{-# BUILTIN NATURAL ℕ #-}

record Unit : Set where
  constructor ⟨⟩
  
data Void : Set where

data Fin : ℕ → Set where
  ze : ∀ {n} → Fin (su n)
  su : ∀ {n} (i : Fin n) → Fin (su n)

data _⋆ (A : Set) : Set where
  · : A ⋆
  _,_ : A ⋆ → A → A ⋆
infixl 8 _,_

tail : ∀ {A} → A ⋆ → A ⋆
tail · = ·
tail (Γ , _) = Γ

∣_∣ : ∀ {A} → A ⋆ → ℕ
∣ · ∣ = ze
∣ Γ , _ ∣ = su ∣ Γ ∣

data hyp {A : Set} : A ⋆ → A → Set where
  ze : ∀ {Γ X} → hyp (Γ , X) X
  su : ∀ {Γ X Y} → hyp Γ X → hyp (Γ , X) Y

∣_∣hyp : {A : Set} {Γ : A ⋆} {X : A} → hyp Γ X → Fin ∣ Γ ∣
∣ ze ∣hyp = ze
∣ su i ∣hyp = su ∣ i ∣hyp

data Canonicity : Set where
  Can Ncan : Canonicity
  
record Op (c : Canonicity) (o : Ident) : Set where
  field
    arity : ℕ ⋆

arity : {c : Canonicity} (oid : Ident) {{_ : Op c oid}} → ℕ ⋆
arity _ {{o}} = Op.arity o

mutual
  data Arguments : ℕ ⋆ → Set where
    · : Arguments ·
    _,_ : ∀ {Γ n} → Arguments Γ → Term n → Arguments (Γ , n)
  
    -- TODO: fix arguments to add n to the valence of each argument
    
  data Term (n : ℕ) : Set where
    `_ : Fin n → Term n
    _$_ : (oid : Ident) {{_ : Op Can oid}} → Arguments (arity oid) → Term n
    _∙_$_ : Term n → (oid : Ident) {{_ : Op Ncan oid}} → Arguments (arity oid) → Term n

mutual
  instantiate1 : ∀ {n} → Term (su n) → Term n → Term n
  instantiate1 (` ze) y = y
  instantiate1 (` su x) _ = ` x
  instantiate1 (oid $ xs) y = oid $ {!!}
  instantiate1 (x ∙ oid $ x₂) y = {!!}

record _prop (P : Term 0) : Set₁ where
  inductive
  field
    icode : Set
    ⟦_⟧i : icode → Σ Ident (Op Can)
    ichk : (o : icode) (let ⟨ oid , _ ⟩ = ⟦ o ⟧i) → Arguments (arity oid) → Set

    ecode : Set
    ⟦_⟧e : ecode → Σ Ident (Op Ncan)
    purpose : (o : ecode) (let ⟨ oid , _ ⟩ = ⟦ o ⟧e) → Arguments (arity oid) → Σ (Term 0) _prop
    echk : (o : ecode) (let ⟨ oid , _ ⟩ = ⟦ o ⟧e) → Arguments (arity oid) → Set

    red : (e : ecode) (let ⟨ eid , _ ⟩ = ⟦ e ⟧e) → Arguments (arity eid) → (i : icode) (let ⟨ iid , _ ⟩ = ⟦ i ⟧i) → Arguments (arity iid) → Term 0

mutual
  data _↝_ : ∀ {n} → Term n → Term n → Set where
    red : ∀ P {{P-prop : P prop}} (let open _prop P-prop) (e : ecode) (let ⟨ eid , _ ⟩ = ⟦ e ⟧e) {es : Arguments (arity eid)} (i : icode) (let ⟨ iid , _ ⟩ = ⟦ i ⟧i) {is : Arguments (arity iid)} → ((iid $ is) ∙ eid $ es) ↝ red e es i is
    trans : ∀ {n} {M N O : Term n} → M ↝ N → N ↝ O → M ↝ O
    can : ∀ {n} P {{P-prop : P prop}} (let open _prop P-prop) (i : icode) (let ⟨ iid , _ ⟩ = ⟦ i ⟧i) {is : Arguments (arity iid)} → _↝_ {n} (iid $ is) (iid $ is)

  data _⊢_⇒ (Γ : Term 0 ⋆) : Term ∣ Γ ∣ → Set₁ where
    `_ : ∀ {P} {{_ : P prop}} (h : hyp Γ P) → Γ ⊢ ` ∣ h ∣hyp ⇒
    _∙_$_by_ : ∀ {R} (D : Γ ⊢ R ⇒) (let open _prop (Σ.snd (synthesis D))) (o : ecode) (let ⟨ oid , _ ⟩ = ⟦ o ⟧e) (xs : Arguments (arity oid)) → echk o xs → Γ ⊢ R ∙ oid $ xs ⇒ 
  
  synthesis : ∀ {Γ R} → Γ ⊢ R ⇒ → Σ (Term 0) _prop
  synthesis (`_ {A} {{A-prop}} _) = ⟨ A , A-prop ⟩
  synthesis (D ∙ o $ xs by _) = let open _prop (Σ.snd (synthesis D)) in purpose o xs

data _⊢_⇐_ (Γ : Term 0 ⋆) (M : Term ∣ Γ ∣) : (P : Term 0) {{_ : P prop}} → Set₁ where
  _$⟨_,_⟩via_ : ∀ {P} {{P-prop : P prop}} (let open _prop P-prop) (o : icode) (let ⟨ oid , _ ⟩ = ⟦ o ⟧i) (xs : Arguments (arity oid)) → ichk o xs → M ↝ (oid $ xs) → Γ ⊢ M ⇐ P

instance
  ⊤-op : Op Can "⊤"
  ⊤-op = record { arity = · }

  tt-op : Op Can "tt"
  tt-op = record { arity = · } 

  ⊤-prop : ("⊤" $ ·) prop
  ⊤-prop = record
    { icode = Unit
    ; ⟦_⟧i = λ _ → [ "tt" ]
    ; ichk = λ _ _ → Unit
    ; ecode = Void
    ; ⟦_⟧e = λ { () }
    ; purpose = λ { () x }
    ; echk = λ { () x }
    ; red = λ { () x i x₁ }
    }

  prod-op : Op Can "prod"
  prod-op = record { arity = · , 0 , 0 }

  pair-op : Op Can "pair"
  pair-op = record { arity = · , 0 , 0 }

  fst-op : Op Ncan "fst"
  fst-op = record { arity = · }

  snd-op : Op Ncan "snd"
  snd-op = record { arity = · }

  prod-prop : {P Q : Term 0} {{_ : P prop}} {{_ : Q prop}} → ("prod" $ (· , P , Q)) prop
  prod-prop {P} {Q} {{_}} {{_}} = record
    { icode = Unit
    ; ⟦_⟧i = λ _ → [ "pair" ]
    ; ichk = λ {⟨⟩ (· , M , N) → Σ (· ⊢ M ⇐ P) λ _ → · ⊢ N ⇐ Q}
    ; ecode = Bool
    ; ⟦_⟧e = λ { tt → [ "fst" ] ; ff → [ "snd" ] }
    ; purpose = λ { tt · → [ P ] ; ff · → [ Q ] }
    ; echk = λ _ _ → Unit
    ; red = λ { tt · ⟨⟩ (· , M , N) → M ; ff · ⟨⟩ (· , M , N) → N }
    }

  ⊃-op : Op Can "⊃" 
  ⊃-op = record { arity = · , 0 , 0 }

  λ-op : Op Can "λ"
  λ-op = record { arity = · , 1 }

  ap-op : Op Ncan "ap"
  ap-op = record { arity = · , 0 }

  ⊃-prop : {P Q : Term 0} {{_ : P prop}} {{_ : Q prop}} → ("⊃" $ (· , P , Q)) prop
  ⊃-prop {P} {Q} {{_}} {{_}} = record
    { icode = Unit
    ; ⟦_⟧i = λ _ → [ "λ" ]
    ; ichk = λ { ⟨⟩ (· , E) → (· , P) ⊢ E ⇐ Q}
    ; ecode = Unit
    ; ⟦_⟧e = λ _ → [ "ap" ]
    ; purpose = λ _ _ → [ Q ]
    ; echk = λ _ _ → Unit
    ; red = λ { ⟨⟩ (· , N) ⟨⟩ (· , E) → {!!} }
    }
    
welp : · ⊢ "tt" $ · ⇐ ("⊤" $ ·)
welp = ⟨⟩ $⟨ · , ⟨⟩ ⟩via can ("⊤" $ ·) ⟨⟩

welp2 : · ⊢ ("pair" $ (· , "tt" $ · , "tt" $ ·)) ∙ "snd" $ · ⇐ ("⊤" $ ·)
welp2 = ⟨⟩ $⟨ · , ⟨⟩ ⟩via red ("prod" $ (· , "⊤" $ · , "⊤" $ ·)) ff ⟨⟩
