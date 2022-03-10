import Agda.Builtin.String
open import Agda.Builtin.Bool using (true ; false ; Bool)
open import Agda.Builtin.Equality using (_≡_ ; refl)
open import Agda.Builtin.Maybe using (Maybe ; nothing ; just)
import Data.List
open import Data.Nat as ℕ using (ℕ; _+_; _<_; s≤s; z≤n; _*_; _∸_; _≤_)
open import Relation.Nullary using (_because_ ; ofʸ ; ofⁿ ; ¬_)
open import Data.Empty using (⊥ ; ⊥-elim)
open import Data.Product using (_,_ ; _×_ ; proj₁ ; proj₂)
import Data.List.Properties
open import Data.List using (List ; [] ; [_] ; _∷_ ; _++_)
open import Data.List.Relation.Unary.Any using (here; there)
import Data.List.Membership.Propositional.Properties
open import Data.Sum using (_⊎_ ; inj₁ ; inj₂)

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

eq-unif-in-mctx : ∀{x y} {Γ : mctx} → unif x ∈' Γ → unif y ∈' Γ → checkeq x y
eq-unif-in-mctx (here refl) (here refl) = true refl
eq-unif-in-mctx (here _) (there _) = false
eq-unif-in-mctx (there _) (here _) = false
eq-unif-in-mctx (there x) (there y) = eq-unif-in-mctx x y



data const : typ → Set where
  a : const o
  b : const o
  f : const (o ⇒ o)
  g : const (o ⇒ (o ⇒ o))

rotate : ∀{@erased x} → const x → const x
rotate a = b
rotate b = a
rotate f = f
rotate g = g

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
data spine (Δ : mctx) (Γ : typctx) : typ → typ → Set
data subst (Δ : mctx) (Γ : typctx) : typctx → Set

data term Δ Γ where
  lambda : ∀ {ρ τ} → term Δ (ρ ∷ Γ) τ → term Δ Γ (ρ ⇒ τ)
  root : ∀ {τ} → head Δ Γ τ → spine Δ Γ τ o → term Δ Γ o 
  mvar : ∀ {Ψ} → unif Ψ ∈' Δ → subst Δ Γ Ψ → term Δ Γ o 
  hole : ∀ {τ} → term Δ Γ τ -- placeholder, page 92

data spine Δ Γ where
  nil : ∀ {τ} → spine Δ Γ τ τ
  cons : ∀ {τ ρ υ} → term Δ Γ τ → spine Δ Γ ρ υ → spine Δ Γ (τ ⇒ ρ) υ

data subst Δ Γ where
  nil : subst Δ Γ []
  sm : ∀ {Ψ τ} → term Δ Γ τ → subst Δ Γ Ψ → subst Δ Γ (τ ∷ Ψ)
  sr : ∀ {Ψ τ} → τ ∈ Γ → subst Δ Γ Ψ → subst Δ Γ (τ ∷ Ψ)

example : term [] [] (o ⇒ (o ⇒ (o ⇒ ((o ⇒ o) ⇒ (o ⇒ o)))))
example = lambda (lambda (lambda (lambda (lambda (root (var (there (here refl))) (cons (root (var (here refl)) nil) nil))))))

snoc-spine : ∀ {Δ Γ τ ρ υ} → term Δ Γ τ → spine Δ Γ ρ (τ ⇒ υ) → spine Δ Γ ρ υ
snoc-spine n nil = cons n nil
snoc-spine n (cons m s) = cons m (snoc-spine n s)

weaken-var : ∀ Ψ {Γ τ ρ} → τ ∈ Ψ ++ Γ → τ ∈ Ψ ++ [ ρ ] ++ Γ
weaken-var [] x = there x
weaken-var (_ ∷ Ψ) (here refl) = here refl
weaken-var (_ ∷ Ψ) (there x) = there (weaken-var Ψ x)

weaken-head : ∀ {Δ Γ} Ψ {τ ρ} → head Δ (Ψ ++ Γ) τ → head Δ (Ψ ++ [ ρ ] ++ Γ) τ
weaken-head Ψ (var x) = var (weaken-var Ψ x) 
weaken-head Ψ (con c) = con c
weaken-head Ψ (free u) = free u

weaken : ∀ {Δ Γ} Ψ {τ ρ} → term Δ (Ψ ++ Γ) τ → term Δ (Ψ ++ [ ρ ] ++ Γ) τ
weaken-spine : ∀ {Δ Γ} Ψ {τ τ' ρ} → spine Δ (Ψ ++ Γ) τ τ' → spine Δ (Ψ ++ [ ρ ] ++ Γ) τ τ' 
weaken-subst : ∀ {Δ Γ Ψ'} Ψ {ρ} → subst Δ (Ψ ++ Γ) Ψ' → subst Δ (Ψ ++ [ ρ ] ++ Γ) Ψ'

weaken Ψ (lambda n) = lambda (weaken (_ ∷ Ψ) n)
weaken Ψ (root h s) = root (weaken-head Ψ h) (weaken-spine Ψ s)
weaken Ψ (mvar u σ) = mvar u (weaken-subst Ψ σ)
weaken Ψ hole = hole

weaken-spine Ψ nil = nil
weaken-spine Ψ (cons n s) = cons (weaken Ψ n) (weaken-spine Ψ s)

weaken-subst Ψ nil = nil
weaken-subst Ψ (sm n σ) = sm (weaken Ψ n) (weaken-subst Ψ σ)
weaken-subst Ψ (sr x σ) = sr (weaken-var Ψ x) (weaken-subst Ψ σ)

eta-expand : ∀ {Δ Γ ρ} τ → head Δ Γ ρ → spine Δ Γ ρ τ → term Δ Γ τ
eta-expand o h s = root h s
eta-expand (τ ⇒ τ₁) h s =
  lambda
    (eta-expand τ₁
      (weaken-head [] h)
      (snoc-spine (eta-expand τ (var (here refl)) nil) (weaken-spine [] s)))

hsubst : ∀ {Δ Γ} Ψ {τ ρ} → term Δ (Ψ ++ Γ) τ → term Δ (Ψ ++ [ τ ] ++ Γ) ρ → term Δ (Ψ ++ Γ) ρ 
hsubst-spine : ∀ {Δ Γ} Ψ {τ ρ ρ'} → term Δ (Ψ ++ Γ) τ → spine Δ (Ψ ++ [ τ ] ++ Γ) ρ ρ' → spine Δ (Ψ ++ Γ) ρ ρ'
hsubst-subst : ∀ {Δ Γ} Ψ {τ Ψ'} → term Δ (Ψ ++ Γ) τ → subst Δ (Ψ ++ [ τ ] ++ Γ) Ψ' → subst Δ (Ψ ++ Γ) Ψ'

reduce : ∀ {Δ Γ τ} → term Δ Γ τ → spine Δ Γ τ o → term Δ Γ o

hsubst Ψ n (lambda m) = lambda (hsubst (_ ∷ Ψ) (weaken [] n) m)
hsubst Ψ n (root (var x) s) with  Data.List.Membership.Propositional.Properties.∈-++⁻ Ψ x
... | inj₂ (here refl) = reduce n (hsubst-spine Ψ n s)
... | inj₁ y = root (var (Data.List.Membership.Propositional.Properties.∈-++⁺ˡ y)) (hsubst-spine Ψ n s)
... | inj₂ (there y) = root (var (Data.List.Membership.Propositional.Properties.∈-++⁺ʳ Ψ y)) (hsubst-spine Ψ n s)
hsubst Ψ n (root (con c) s) = root (con c) (hsubst-spine Ψ n s)
hsubst Ψ n (root (free u) s) = root (free u) (hsubst-spine Ψ n s)
hsubst Ψ n (mvar u σ) = mvar u (hsubst-subst Ψ n σ)
hsubst Ψ n hole = hole

hsubst-spine Ψ n nil = nil
hsubst-spine Ψ n (cons m s) = cons (hsubst Ψ n m) (hsubst-spine Ψ n s)

hsubst-subst Ψ n nil = nil
hsubst-subst Ψ n (sm m σ) = sm (hsubst Ψ n m) (hsubst-subst Ψ n σ)
hsubst-subst Ψ n (sr x σ) with Data.List.Membership.Propositional.Properties.∈-++⁻ Ψ x
... | inj₂ (here refl) = sm n (hsubst-subst Ψ n σ)
... | inj₁ y = sr (Data.List.Membership.Propositional.Properties.∈-++⁺ˡ y) (hsubst-subst Ψ n σ)
... | inj₂ (there y) = sr (Data.List.Membership.Propositional.Properties.∈-++⁺ʳ Ψ y) (hsubst-subst Ψ n σ)

reduce (lambda n) (cons m s) = reduce (hsubst [] m n) s
reduce n nil = n
reduce hole s = hole

get-subst : ∀ {Δ Ψ Γ τ} → τ ∈ Ψ → subst Δ Γ Ψ → (τ ∈ Γ) ⊎ (term Δ Γ τ)
get-subst (here refl) (sr x σ) = inj₁ x
get-subst (here refl) (sm x σ) = inj₂ x
get-subst (there x) (sm _ σ) = get-subst x σ
get-subst (there x) (sr _ σ) = get-subst x σ

apply-subst : ∀ {Δ Γ Ψ τ} → subst Δ Γ Ψ → term Δ Ψ τ → term Δ Γ τ
apply-subst-spine : ∀ {Δ Γ Ψ τ ρ} → subst Δ Γ Ψ → spine Δ Ψ τ ρ → spine Δ Γ τ ρ
apply-subst-subst : ∀ {Δ Γ Ψ Ψ'} → subst Δ Γ Ψ → subst Δ Ψ Ψ' → subst Δ Γ Ψ'

apply-subst σ (lambda trm) = lambda (apply-subst (sr (here refl) (weaken-subst [] σ)) trm)
apply-subst σ (root (var x) s) with get-subst x σ
... | inj₁ y = root (var y) (apply-subst-spine σ s)
... | inj₂ n = reduce n (apply-subst-spine σ s)
apply-subst σ (root (con c) s) = root (con c) (apply-subst-spine σ s)
apply-subst σ (root (free m) s) = root (free m) (apply-subst-spine σ s)
apply-subst σ (mvar u σ') = mvar u (apply-subst-subst σ σ')
apply-subst σ hole = hole

apply-subst-spine σ nil = nil
apply-subst-spine σ (cons n s) = cons (apply-subst σ n) (apply-subst-spine σ s)

apply-subst-subst σ nil = nil
apply-subst-subst σ (sm n σ') = sm (apply-subst σ n) (apply-subst-subst σ σ')
apply-subst-subst σ (sr x σ') with get-subst x σ
... | inj₁ y = sr y (apply-subst-subst σ σ')
... | inj₂ n = sm n (apply-subst-subst σ σ')


-- invert-var : τ ∈ Ψ → subst Δ Γ Ψ →

{-
strengthen-pattern-subst : ∀ {Δ Γ τ Ψ} → subst Δ (τ ∷ Γ) Ψ → Maybe (subst Δ Γ Ψ)
strengthen-pattern-subst nil =  just nil
strengthen-pattern-subst (sm _ _) = nothing
strengthen-pattern-subst (sr (here _) _) = nothing
strengthen-pattern-subst (sr (there x) σ) with strengthen-pattern-subst σ
... | just σ = just (sr x σ)
... | nothing = nothing

invert-var : ∀ {Δ Γ τ Ψ} → subst Δ (τ ∷ Γ) Ψ → Maybe (τ ∈ Ψ × subst Δ (τ ∷ Γ) Ψ)
invert-var nil = nothing
invert-var (sm x σ) = nothing
invert-var (sr (here refl) σ) = just (here refl , sr (here refl) σ)
invert-var (sr (there x) σ) with invert-var σ
... | nothing = nothing
... | just (y , σ') = just (there y , sr (there x) σ')
-}

rigid-hole : ∀ {Δ Γ τ} → term Δ Γ τ → Bool
rigid-hole-spine : ∀ {Δ Γ τ} → spine Δ Γ τ o → Bool

rigid-hole (lambda n) = rigid-hole n
rigid-hole (root h s) = rigid-hole-spine s
rigid-hole (mvar u σ) = false
rigid-hole hole = true

rigid-hole-spine nil = false
rigid-hole-spine (cons n s) with rigid-hole n
... | true = true
... | false = rigid-hole-spine s


invert-var : ∀ {Δ Γ τ Ψ} → τ ∈ Γ → subst Δ Γ Ψ → Maybe (τ ∈ Ψ)
invert-var x nil = nothing
invert-var x (sm _ _) = nothing
invert-var x (sr x' σ) with eqinctx x x'
... | true refl = just (here refl)
... | false with invert-var x σ
... | nothing = nothing
... | just y = just (there y)

_⊆_ : typctx → typctx → Set
_⊆_ Γ Γ' = ∀ {τ} → τ ∈ Γ → τ ∈ Γ'

invert-subst : ∀ {Δ Ψ Γ'} (Γ) → Γ ⊆ Γ' → subst Δ Γ' Ψ → Maybe (subst Δ Ψ Γ)
invert-subst [] pf σ = just nil
invert-subst (x ∷ Γ) pf σ with invert-subst Γ (λ y → pf (there y)) σ
... | nothing = nothing
... | just σ' with invert-var (pf (here refl)) σ
... | nothing = nothing
... | just y = just (sr y σ')

{-
invert-subst [] ξ = just nil
invert-subst {Δ} {Ψ} (τ ∷ Γ) ξ with invert-var ξ
... | nothing = nothing
... | just (x , ξ') with invert-subst Γ {!ξ'!}
... | nothing = nothing
... | just ξ'' = just (sr x ξ'')
-}
{- with invert-subst {Δ} {Ψ} Γ {! !}
... | nothing = nothing
... | just ξ' = just (sr {!!} ξ') -}

data eqn (Δ : mctx) : Set where
  unifyTerm : ∀ {Γ τ} → term Δ Γ τ → term Δ Γ τ → eqn Δ -- M ≐ M'
  unifyMvar : ∀{Γ} → unif Γ ∈' Δ → term Δ Γ o → eqn Δ -- u ≐ R

data eqns (Δ : mctx) : Set where
  nil : eqns Δ
  _∧_ : eqn Δ → eqns Δ → eqns Δ

_∧'_ : ∀ {Δ} → eqn Δ → Maybe (eqns Δ × Bool) → Maybe (eqns Δ × Bool)
P ∧' Q with Q
... | nothing = nothing
... | just (Q' , _) = just (P ∧ Q' , true)

_∧?_ : ∀ {Δ} → eqn Δ → Maybe (eqns Δ × Bool) → Maybe (eqns Δ × Bool)
P ∧? Q with Q
... | nothing = nothing
... | just (Q' , progress) = just (P ∧ Q' , progress)

data simplified (Δ : mctx) : Set where
  stalled : List (eqn Δ) → simplified Δ
  progress : List (eqn Δ) → simplified Δ
  failure : simplified Δ
  assign : ∀ {Ψ} → unif Ψ ∈' Δ → term Δ Ψ o → List (eqn Δ) → simplified Δ -- u ← R

simplify-spine : ∀ {Δ Γ τ} → spine Δ Γ τ o → spine Δ Γ τ o → List (eqn Δ)
simplify-spine nil nil = []
simplify-spine (cons n s) (cons n' s') = unifyTerm n n' ∷ simplify-spine s s'

simplify-one : ∀ {Δ} → eqn Δ → simplified Δ
-- Decomposition and inversion
simplify-one (unifyTerm (lambda m) (lambda m')) = progress [ unifyTerm m m' ]
simplify-one (unifyTerm (root h s) (root h' s')) with eqhead h h'
... | true refl = progress (simplify-spine s s')
... | false = failure
simplify-one (unifyTerm hole _) = failure
simplify-one (unifyTerm _ hole) = failure
simplify-one (unifyMvar _ hole) = failure
simplify-one (unifyTerm (root h s) (mvar u σ)) = progress [ unifyTerm (mvar u σ) (root h s)  ]
simplify-one (unifyTerm (mvar u σ) (root h s)) with rigid-hole (root h s)
... | true = failure
... | false = stalled [ unifyTerm (mvar u σ) (root h s) ] -- TODO inversion
simplify-one (unifyTerm (mvar u σ) (mvar u' σ')) = stalled [ unifyTerm (mvar u σ) (mvar u' σ') ] -- TODO inversion

-- TODO intersection, pruning, instantiation
simplify-one (unifyMvar u (root h s)) with rigid-hole (root h s)
... | true = failure
... | false = stalled [ unifyMvar u (root h s) ]
simplify-one (unifyMvar u (mvar u' σ)) = stalled [ unifyMvar u (mvar u' σ) ]

simplify-something : ∀ {Δ} → List (eqn Δ) → simplified Δ
simplify-something [] = stalled []
simplify-something (P ∷ Q) with simplify-one P
... | progress P' = progress (P' ++ Q)
... | failure = failure
... | assign u r P' = assign u r (P' ++ Q)
... | stalled P' with simplify-something Q
... | stalled Q' = stalled (P' ++ Q')
... | progress Q' = progress (P' ++ Q')
... | failure = failure
... | assign u r Q' = assign u r (P' ++ Q')


problem1 : List (eqn [ unif (o ∷ o ∷ []) ])
problem1 = [ unifyTerm {Γ = []} (lambda (lambda (root (con f) (cons (root (var (here refl)) nil) nil)))) (lambda(lambda (root (con f) (cons (mvar (here refl) (sr (there (here refl)) (sr (here refl) nil))) nil)))) ]

{-
simplify-one nil = just (nil , false)
simplify-one (assign u R ∧ rest) = assign u R ∧' simplify-one rest

-- Decomposition
simplify (unifyTerm (lambda M) (lambda M') ∧ rest) = unifyTerm M M' ∧' simplify rest
simplify (unifyTerm (root H S) (root H' S') ∧ rest) with eqhead H H'
... | true refl = unifySpine S S' ∧' simplify rest
... | false = nothing
simplify (unifySpine (cons M S) (cons M' S') ∧ rest) = unifyTerm M M' ∧' (unifySpine S S' ∧' simplify rest) 
simplify (unifySpine nil nil ∧ rest) = simplify rest
simplify (unifyTerm _ hole ∧ rest) = nothing
simplify (unifyTerm hole _ ∧ rest) = nothing
simplify (unifyMvar _ hole ∧ rest) = nothing

-- Inversion
simplify (unifyTerm R (mvar u ξ) ∧ rest) = unifyMvar u (apply-subst {!ξ!} R) ∧' simplify rest
simplify (unifyTerm (mvar u ξ) R ∧ rest) = unifyMvar u {!!} ∧' simplify rest

-- Occurs check
simplify (unifyMvar u (root H S) ∧ rest) = {!!}

simplify (unifyMvar u (mvar v σ) ∧ rest) with eq-unif-in-mctx u v
... | true refl = {!!}
-- Intersection
... | false = {!!}
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
