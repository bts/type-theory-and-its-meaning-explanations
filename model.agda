-- The is an example of the kind of meaning explanations I intend to
-- give for the verifications & uses type theory. For simplicity, I
-- have restricted the term language to include only normal terms, but
-- one would of course extend this to have all terms, and a proper
-- reduction relation.

module model where

data prop : Set where
  ⊤ ⊥ : prop
  _&_ _⊃_ : prop → prop → prop

data _==_prop : prop → prop → Set where
  ⊤ : ⊤ == ⊤ prop
  ⊥ : ⊥ == ⊥ prop
  _&_ : ∀ {A A′ B B′} → A == A′ prop → B == B′ prop → (A & B) == (A′ & B′) prop
  _⊃_ : ∀ {A A′ B B′} → A == A′ prop → B == B′ prop → (A ⊃ B) == (A′ ⊃ B′) prop

data ℕ : Set where
  ze : ℕ
  su : ℕ → ℕ

data Fin : ℕ → Set where
  ze : ∀ {n} → Fin (su n)
  su : ∀ {n} (i : Fin n) → Fin (su n)

data _⋆ (A : Set) : Set where
  · : A ⋆
  _,_ : A ⋆ → A → A ⋆
infixl 8 _,_

∣_∣ : ∀ {A} → A ⋆ → ℕ
∣ · ∣ = ze
∣ Γ , _ ∣ = su ∣ Γ ∣

data hyp {A : Set} : A ⋆ → A → Set where
  ze : ∀ {Γ X} → hyp (Γ , X) X
  su : ∀ {Γ X Y} → hyp Γ X → hyp (Γ , X) Y

∣_∣hyp : {A : Set} {Γ : A ⋆} {X : A} → hyp Γ X → Fin ∣ Γ ∣
∣ ze ∣hyp = ze
∣ su i ∣hyp = su ∣ i ∣hyp

mutual 
  data can (n : ℕ) : Set where
    tt : can n
    ⟨_,_⟩ : nrm n → nrm n → can n
    []_ : nrm (su n) → can n

  data elim (n : ℕ) : Set where
    abort[_] : prop → elim n
    fst snd : elim n
    ap : nrm n → elim n

  data neu (n : ℕ) : Set where
    `_ : Fin n → neu n
    _•_ : neu n → elim n → neu n

  data nrm (n : ℕ) : Set where
    ⌜_⌝ : can n → nrm n
    ⌞_⌟ : neu n → nrm n

mutual

  -- Canonical verifications
  data _⊢_verifies_ (Γ : prop ⋆) : can ∣ Γ ∣ → prop → Set where
    tt : Γ ⊢ tt verifies ⊤
    ⟨_,_⟩ : ∀ {A B M N} → Γ ⊢ M ↓ A → Γ ⊢ N ↓ B → Γ ⊢ ⟨ M , N ⟩ verifies (A & B)
    []_ : ∀ {A B E} → (Γ , A) ⊢ E ↓ B → Γ ⊢ ([] E) verifies (A ⊃ B)

  -- Direct/immediate(?) uses
  data _⊢_uses_ (Γ : prop ⋆) : elim ∣ Γ ∣ → prop → Set where
    abort[_] : (A : prop) → Γ ⊢ abort[ A ] uses ⊥
    fst : ∀ {A B} → Γ ⊢ fst uses (A & B)
    snd : ∀ {A B} → Γ ⊢ snd uses (A & B)
    ap : ∀ {A B} {M} → Γ ⊢ M ↓ A → Γ ⊢ ap M uses (A ⊃ B) 

  -- The evidence for the judgmeent (E uses P) will be the purpose for the use
  purpose : ∀ {A Γ} {E : elim ∣ Γ ∣} → Γ ⊢ E uses A → prop
  purpose abort[ A ] = A
  purpose (fst {A} {_}) = A
  purpose (snd {_} {B}) = B
  purpose (ap {_} {B} M) = B


  -- synthesis for neutral terms
  data _⊢_↑ (Γ : prop ⋆) : neu ∣ Γ ∣ → Set where
    `_ : ∀ {A} (h : hyp Γ A)→ Γ ⊢ ` ∣ h ∣hyp ↑
    _•_ : ∀ {E R} (D : Γ ⊢ R ↑) (u : Γ ⊢ E uses (synthesis D)) → Γ ⊢ R • E ↑

  -- the evidence for Γ ⊢ R ↑ is the synthesized type
  synthesis : ∀ {Γ R} → Γ ⊢ R ↑ → prop
  synthesis (`_ {A} _) = A
  synthesis (D • u) = purpose u

  -- checking for normal terms
  data _⊢_↓_ (Γ : prop ⋆) : nrm ∣ Γ ∣ → prop → Set where
    ⌜_⌝ : ∀ {M A} → Γ ⊢ M verifies A → Γ ⊢ ⌜ M ⌝ ↓ A
    ⌞_⌟ : ∀ {R A} (D : Γ ⊢ R ↑) {{_ : synthesis D == A prop}} → Γ ⊢ ⌞ R ⌟ ↓ A

-- an example
test : · ⊢ ⌜ [] ⌞ ` ze • fst ⌟ ⌝ ↓ ((⊤ & ⊥) ⊃ ⊤)
test = ⌜ [] ⌞ ` ze • fst ⌟ ⌝
