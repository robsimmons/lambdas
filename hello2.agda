import Agda.Builtin.String
open import Agda.Builtin.Bool using (true ; false)
open import Agda.Builtin.Equality using (_≡_ ; refl)
open import Agda.Builtin.Maybe using (Maybe ; nothing ; just)
import Data.List
open import Data.Nat as ℕ using (ℕ; _+_; _<_; s≤s; z≤n; _*_; _∸_; _≤_)
open import Relation.Nullary using (_because_ ; ofʸ ; ofⁿ ; ¬_)
open import Data.Empty using (⊥ ; ⊥-elim)
open import Data.Product using (_,_ ; _×_ ; proj₁ ; proj₂)
import Data.List.Properties
open import Data.List using (List ; [] ; _∷_ ; _++_)
import Data.List.Membership.Propositional.Properties

data typ : Set where
  o : typ
  _⇒_ : typ → typ → typ
typctx = List typ

⇒-injective : ∀ {τ ρ τ' ρ'} → (τ ⇒ ρ) ≡ (τ' ⇒ ρ') → (τ ≡ τ') × (ρ ≡ ρ')
⇒-injective refl = (refl , refl)

≡-dec-typ : (τ : typ) (ρ : typ) → Relation.Nullary.Dec (τ ≡ ρ)
≡-dec-typ o o = true because ofʸ refl
≡-dec-typ o (ρ ⇒ ρ₁) = false because ofⁿ (λ ())
≡-dec-typ (τ ⇒ τ₁) o = false because ofⁿ (λ ())
≡-dec-typ (τ ⇒ τ₁) (ρ ⇒ ρ₁) with ≡-dec-typ τ ρ | ≡-dec-typ τ₁ ρ₁
... | false because ofⁿ ¬p | _ = false because (ofⁿ λ p → ¬p (proj₁ (⇒-injective p)))
... | _ | false because ofⁿ ¬p = false because (ofⁿ λ p → ¬p (proj₂ (⇒-injective p)))
... | true because ofʸ refl | true because ofʸ refl = true because ofʸ refl
open import Data.List.Membership.DecPropositional (≡-dec-typ) as CtxMembership using (_∈_)


data modaltyp : Set where
  unif : typctx → modaltyp -- Ψ ⊢ o, page 88
  free : typ → modaltyp -- Free variable, page 93
mctx = List modaltyp

unif-injective : ∀ {Ψ Ψ'} → unif Ψ ≡ unif Ψ' → Ψ ≡ Ψ'
unif-injective refl = refl

free-injective : ∀ {τ τ'} → free τ ≡ free τ' → τ ≡ τ'
free-injective refl = refl

≡-dec-modaltyp : (j : modaltyp) (k : modaltyp) → Relation.Nullary.Dec (j ≡ k)
≡-dec-modaltyp (unif Ψ₁) (unif Ψ₂) with Data.List.Properties.≡-dec  ≡-dec-typ Ψ₁ Ψ₂
... | false because ofⁿ ¬p = false because ofⁿ (λ p → ¬p (unif-injective p))
... | true because ofʸ refl = true because ofʸ refl
≡-dec-modaltyp (free τ₁) (free τ₂) with ≡-dec-typ τ₁ τ₂
... | false because ofⁿ ¬p = false because ofⁿ (λ p → ¬p (free-injective p))
... | true because ofʸ refl = true because ofʸ refl
≡-dec-modaltyp (unif x) (free x₁) = false because ofⁿ (λ ())
≡-dec-modaltyp (free x) (unif x₁) = false because ofⁿ (λ ())


open import Data.List.Membership.DecPropositional (≡-dec-modaltyp) as MCtxMembership renaming (_∈_ to _∈'_)

open import Data.List.Relation.Unary.Any using (here; there)
lem₁ : o ∈ o ∷ o ∷ o ∷ []
lem₁ = there (here refl)

data checkeq {A} : (x y : A) → Set    where
  true : ∀ {x y} → x ≡ y → checkeq x y
  false : ∀ {x y} → checkeq x y

eqinctx : ∀{x y} {Γ : typctx} → x ∈ Γ → y ∈ Γ → checkeq x y
eqinctx (here refl) (here refl) = true refl
eqinctx (here px) (there y) = false
eqinctx (there x) (here px) = false
eqinctx (there x) (there y) = eqinctx x y

eq-free-in-mctx : ∀{x y} {Γ : mctx} → free x ∈' Γ → free y ∈' Γ → checkeq x y
eq-free-in-mctx (here refl) (here refl) = true refl
eq-free-in-mctx (here _) (there _) = false
eq-free-in-mctx (there _) (here _) = false
eq-free-in-mctx (there x) (there y) = eq-free-in-mctx x y


data const : typ → Set where
  a : const o
  b : const o
  f : const (o ⇒ o)
  g : const (o ⇒ (o ⇒ o))

eqconst : ∀ {τ ρ} → const τ → const ρ → checkeq τ ρ
eqconst a a = true refl
eqconst b b = true refl
eqconst f f = true refl
eqconst g g = true refl
eqconst _ _ = false

data head (Δ : mctx) (Γ : typctx) : typ → Set where
  var : ∀ {τ} → τ ∈ Γ → head Δ Γ τ
  con : ∀ {τ} → const τ → head Δ Γ τ
  free : ∀ {τ} → free τ ∈' Δ → head Δ Γ τ

eqhead : ∀ {Δ Γ τ ρ} → head Δ Γ τ → head Δ Γ ρ → checkeq τ ρ
eqhead (var x) (var x₁) = eqinctx x x₁
eqhead (con x) (con x₁) = eqconst x x₁
eqhead (free x) (free x₁) with eq-free-in-mctx x x₁
... | true refl = true refl
... | false = false
eqhead _ _ = false

data term (Δ : mctx) (Γ : typctx) : typ → Set
data subst (Δ : mctx) (Γ : typctx) : typctx → Set

data term Δ Γ where
  var : ∀ {τ} → τ ∈ Γ → term Δ Γ τ
  _[_] : ∀ {Ψ τ} → term Δ Ψ τ → subst Δ Γ Ψ → term Δ Γ τ
  lam : ∀ {ρ τ} → term Δ (ρ ∷ Γ) τ → term Δ Γ (ρ ⇒ τ)
  app : ∀ {ρ τ} → term Δ Γ (ρ ⇒ τ) → term Δ Γ ρ → term Δ Γ τ

data subst Δ Γ where
  id : subst Δ Γ Γ
  ↑ : ∀{τ Ψ} → subst Δ Γ (τ ∷ Ψ) → subst Δ Γ Ψ
  _·_ : ∀{τ Ψ} → term Δ Γ τ → subst Δ Γ Ψ → subst Δ Γ (τ ∷ Ψ)
  _∘_ : ∀{Ψ Ψ'} → subst Δ Γ Ψ' → subst Δ Ψ' Ψ → subst Δ Γ Ψ
  
{-

data spine (Δ : mctx) (Γ : typctx) : typ → typ → Set

snoc-spine : ∀ {Δ Γ τ ρ υ} → term Δ Γ τ → spine Δ Γ ρ (τ ⇒ υ) → spine Δ Γ ρ υ
snoc-spine x y = {!!}


shift-head : ∀ {Δ Γ} Ψ {τ ρ} → head Δ Γ τ → head Δ (Ψ ++ [ ρ ] ++ Γ) τ
shift-head Ψ (var x) = var (Data.List.Membership.Propositional.Properties.∈-++⁺ʳ Ψ (there x))
shift-head Ψ (con c) = con c
shift-head Ψ (free u) = free u

shift-term : ∀ {Δ Γ} Ψ {τ ρ} → term Δ Γ τ → term Δ (Ψ ++ [ ρ ] ++ Γ) τ
shift-term Ψ (lambda n) = lambda  {!shift-term (_ ∷ Ψ) n!}
shift-term Ψ (root x x₁) = {!!}
shift-term Ψ (mvar x x₁) = {!!}
shift-term Ψ hole = {!!}



weaken-head : ∀ {Δ Γ} Ψ {τ} → head Δ Γ τ → head Δ (Ψ ++ Γ) τ
weaken-head {_} Ψ (var x) = var (Data.List.Membership.Propositional.Properties.∈-++⁺ʳ Ψ x)
weaken-head _ (con x) = con x
weaken-head _ (free x) = free x




weaken-term : ∀ {Δ Γ} Ψ {τ} → term Δ Γ τ → term Δ (Ψ ++ Γ) τ
weaken-spine : ∀ {Δ Γ} Ψ {τ ρ} → spine Δ Γ τ ρ → spine Δ (Ψ ++ Γ) τ ρ

weaken-term Ψ {τ ⇒ ρ} (lambda n) = lambda {! n!}
weaken-term Ψ (root h s) = root (weaken-head Ψ h) (weaken-spine Ψ s)
weaken-term Ψ (mvar u σ) = mvar u {!!}
weaken-term Ψ hole = hole

weaken-spine Ψ nil = nil
weaken-spine Ψ (cons n s) = cons (weaken-term Ψ n) (weaken-spine Ψ s)

eta-expand : ∀ {Δ Γ ρ} τ → head Δ Γ ρ → spine Δ Γ ρ τ → term Δ Γ τ
eta-expand o h s = root h s
eta-expand (τ ⇒ τ₁) h s = lambda (eta-expand τ₁ (weaken-head [ τ ] h) {!!})

weakenSubst : ∀ {Δ Γ Ψ τ} → subst Δ Γ Ψ → subst Δ (τ ∷ Γ) Ψ
weakenSubst nil = nil
weakenSubst (sm x σ) = {!!}
weakenSubst (sr x σ) = {!!}

applySubst : ∀ {Δ Γ Ψ τ} → subst Δ Γ Ψ → term Δ Ψ τ → term Δ Γ τ
applySubst σ (lambda trm) = lambda (applySubst (sr {!!} (weakenSubst σ)) trm)
applySubst σ (root (var x) S) = {!!}
applySubst σ (root (con c) S) = root (con c) {!!}
applySubst σ (root (free m) S) = root (free m) {!!}
applySubst σ (mvar x x₁) = {!!}
applySubst σ hole = {!!}

{-
invertSubst : ∀ {Δ Ψ} (Γ) → subst Δ Γ Ψ → Maybe (subst Δ Ψ Γ)
invertSubst [] ξ = just nil
invertSubst (x ∷ Γ) ξ with invertSubst Γ {!!}
... | nothing = nothing
... | just ξ' = {!!}

ts : term [] [] (o ⇒ o)
ts = lambda (root (var {!!}) nil)

data eqn (Δ : mctx) : Set where
  unifyTerm : ∀{Γ τ} → term Δ Γ τ → term Δ Γ τ → eqn Δ
  unifySpine : ∀{Γ τ} → spine Δ Γ τ o → spine Δ Γ τ o → eqn Δ
  unifyMvar : ∀{Γ} → {!!} → term Δ Γ o → eqn Δ -- unif Γ ∈ Δ 
  assign : ∀{Γ} (u : unif Γ ∈' Δ) → term Δ Γ o → eqn Δ


data eqns (Δ : mctx) : Set where
  nil : eqns Δ
  _∧_ : eqn Δ → eqns Δ → eqns Δ

_∧'_ : ∀ {Δ} → eqn Δ → Maybe (eqns Δ) → Maybe (eqns Δ)
P ∧' Q with Q
... | nothing = nothing
... | just Q' = just (P ∧ Q')

simplify : ∀ {Δ} → eqns Δ → Maybe (eqns Δ)
simplify nil = just nil
simplify (assign u R ∧ rest) = assign u R ∧' simplify rest

-- Decomposition
simplify (unifyTerm (lambda M) (lambda M') ∧ rest) = unifyTerm M M' ∧' simplify rest
simplify (unifyTerm (root H S) (root H' S') ∧ rest) with eqhead H H'
... | true refl = unifySpine S S' ∧' simplify rest
... | false = nothing
simplify (unifySpine (cons M S) (cons M' S') ∧ rest) = unifyTerm M M' ∧' (unifySpine S S' ∧' simplify rest) 
simplify (unifySpine nil nil ∧ rest) = simplify rest
simplify (unifyTerm _ hole ∧ rest) = nothing
simplify (unifyTerm hole _ ∧ rest) = nothing
simplify (unifyMvar u hole ∧ rest) = nothing

-- Inversion
simplify (unifyTerm R (mvar u ξ) ∧ rest) = unifyMvar u {!!} ∧' simplify rest
simplify (unifyTerm (mvar u ξ) R ∧ rest) = unifyMvar u {!!} ∧' simplify rest

-- Occurs check
simplify (unifyMvar u (root H S) ∧ rest) = {!!}

simplify (unifyMvar u (mvar v ξ) ∧ rest) = {!!}
-- Intersection
-- Instantiation
-- Pruning

{-
simplify (unifyTerm (lambda M) (lambda M') ∧ rest) = cons (unifyTerm M M') rest
simplify (cons (unifyTerm (root H S) (root H' S')) rest) = {!!}
simplify (cons (unifySpine nil nil) rest) = {!!}
simplify {Δ} (cons (unifySpine (cons M S) (cons M' S')) rest) = {!cons (unifyTerm M M') (cons (u))!}
simplify (cons (unifyTerm (lambda _) hole) rest) = failure
simplify (cons (unifyTerm (root x x₂) (mvar x₁ x₃)) rest) = {!!}
simplify {Δ} (cons (unifyTerm (root x x₂) hole) rest) = {!!}
simplify {Δ} (cons (unifyTerm (mvar x x₂) x₁) rest) = {!!}
simplify {Δ} (cons (unifyTerm hole x₁) rest) = {!!}
simplify {Δ} (cons (unifyAtom x x₁ x₂ x₃) rest) = {!!}
simplify {Δ} (cons (unifyMvar x x₁) rest) = {!!}
simplify {Δ} (cons (assign x x₁) rest) = {!!}
-}

-}
-}
