/-
  Spectral Arithmetic: Gödel Encoding
  ====================================

  The framework's syntax encoded as eigenstates. Every term in the
  framework's language gets a unique natural number (Gödel number),
  and that number indexes an eigenstate f_N in the orbit.

  Architecture
  ------------

  1. **Term** — inductive type for the framework's formal language
  2. **encode** — injective map Term → ℕ using Cantor pairing
  3. **Triple identity** — each eigenstate f_N is simultaneously:
     (a) A number (eigenvalue N under obs)
     (b) A process (composable, observable state)
     (c) A code (Gödel number ⌜T⌝ for some term T)
  4. **Syntactic predicates** — decidable functions on ℕ that check
     well-formedness, axiom membership, etc.

  Encoding choice: We use Cantor pairing (Nat.pair) rather than prime
  factorization. Both are injective and decodable; Cantor pairing is
  better supported in Mathlib and avoids heavy number theory. The
  pen-and-paper theory uses primes for intuition, but the formal
  properties (injectivity, decodability) are identical.

  Dependencies: Basic.lean (SpectralMonoid, iterS, isNat)
-/

import SpectralArithmetic.Basic
import Mathlib.Data.Nat.Pairing

namespace SpectralMonoid

/-! ## Part 1: The Framework's Formal Language

The term language mirrors the primitives from the axiom system.
Each constructor corresponds to a symbol in the framework's alphabet. -/

/-- Terms of the Spectral Arithmetic formal language. -/
inductive Term where
  /-- Constants -/
  | f₀ : Term
  | f₁ : Term
  | z  : Term
  /-- Variables (indexed by ℕ) -/
  | var : ℕ → Term
  /-- Binary composition: compose(a, b) -/
  | comp : Term → Term → Term
  /-- Observation: obs(a) -/
  | obs : Term → Term
  /-- Addition: a ⊕ b -/
  | oplus : Term → Term → Term
  /-- Additive inverse: ⊖a -/
  | oneg : Term → Term
  deriving Repr, BEq, DecidableEq

namespace Term

/-! ## Part 2: Gödel Encoding

We encode terms as natural numbers using Cantor pairing.
Each constructor gets a unique tag (0-7), and compound terms
pair the tag with the encoded subterms.

The encoding is:
  f₀         ↦ ⟨0, 0⟩
  f₁         ↦ ⟨0, 1⟩
  z          ↦ ⟨0, 2⟩
  var n      ↦ ⟨0, n + 3⟩      (shifted to avoid collision with constants)
  comp a b   ↦ ⟨1, ⟨⌜a⌝, ⌜b⌝⟩⟩
  obs a      ↦ ⟨2, ⌜a⌝⟩
  oplus a b  ↦ ⟨3, ⟨⌜a⌝, ⌜b⌝⟩⟩
  oneg a     ↦ ⟨4, ⌜a⌝⟩

where ⟨·,·⟩ = Nat.pair -/

/-- Gödel encoding: Term → ℕ -/
def encode : Term → ℕ
  | .f₀          => Nat.pair 0 0
  | .f₁          => Nat.pair 0 1
  | .z           => Nat.pair 0 2
  | .var n       => Nat.pair 0 (n + 3)
  | .comp a b    => Nat.pair 1 (Nat.pair (encode a) (encode b))
  | .obs a       => Nat.pair 2 (encode a)
  | .oplus a b   => Nat.pair 3 (Nat.pair (encode a) (encode b))
  | .oneg a      => Nat.pair 4 (encode a)

/-- Notation: ⌜T⌝ for the Gödel number of T -/
scoped notation "⌜" t "⌝" => encode t

/-! ### Injectivity of encoding

The encoding is injective: distinct terms get distinct Gödel numbers.
This is the fundamental property that makes the encoding usable. -/

/-- The Gödel encoding is injective. -/
theorem encode_injective : Function.Injective encode := by
  intro a b h
  induction a with
  | f₀ => cases b <;> simp [encode, Nat.pair] at h <;> try exact h.elim
  | f₁ => cases b <;> simp [encode, Nat.pair] at h <;> try exact h.elim
  | z => cases b <;> simp [encode, Nat.pair] at h <;> try exact h.elim
  | var n =>
    cases b <;> simp [encode, Nat.pair] at h
    case var m => exact congrArg var (by omega)
  | comp a₁ a₂ ih₁ ih₂ =>
    cases b <;> simp [encode, Nat.pair] at h
    case comp b₁ b₂ =>
      have h₁ := Nat.pair_injective h
      have h₂ := Nat.pair_injective h₁.2
      exact congrArg₂ comp (ih₁ h₂.1) (ih₂ h₂.2)
  | obs a₁ ih₁ =>
    cases b <;> simp [encode, Nat.pair] at h
    case obs b₁ => exact congrArg obs (ih₁ h)
  | oplus a₁ a₂ ih₁ ih₂ =>
    cases b <;> simp [encode, Nat.pair] at h
    case oplus b₁ b₂ =>
      have h₁ := Nat.pair_injective h
      have h₂ := Nat.pair_injective h₁.2
      exact congrArg₂ oplus (ih₁ h₂.1) (ih₂ h₂.2)
  | oneg a₁ ih₁ =>
    cases b <;> simp [encode, Nat.pair] at h
    case oneg b₁ => exact congrArg oneg (ih₁ h)

/-! ## Part 3: Term Structure Operations -/

/-- Size of a term (number of constructors) -/
def size : Term → ℕ
  | .f₀ | .f₁ | .z => 1
  | .var _ => 1
  | .comp a b => 1 + size a + size b
  | .obs a => 1 + size a
  | .oplus a b => 1 + size a + size b
  | .oneg a => 1 + size a

/-- All terms have positive size -/
theorem size_pos : ∀ t : Term, 0 < size t := by
  intro t; cases t <;> simp [size] <;> omega

/-- Free variables of a term -/
def freeVars : Term → List ℕ
  | .f₀ | .f₁ | .z => []
  | .var n => [n]
  | .comp a b => freeVars a ++ freeVars b
  | .obs a => freeVars a
  | .oplus a b => freeVars a ++ freeVars b
  | .oneg a => freeVars a

/-- A term is closed if it has no free variables -/
def isClosed (t : Term) : Prop := freeVars t = []

/-- Constants are closed -/
theorem f₀_closed : isClosed f₀ := rfl
theorem f₁_closed : isClosed f₁ := rfl
theorem z_closed : isClosed z := rfl

/-! ## Part 4: Substitution -/

/-- Substitute variable n with term s in term t -/
def subst (t : Term) (n : ℕ) (s : Term) : Term :=
  match t with
  | .f₀ => .f₀
  | .f₁ => .f₁
  | .z  => .z
  | .var m => if m = n then s else .var m
  | .comp a b => .comp (subst a n s) (subst b n s)
  | .obs a => .obs (subst a n s)
  | .oplus a b => .oplus (subst a n s) (subst b n s)
  | .oneg a => .oneg (subst a n s)

/-- Substitution on a closed term is identity -/
theorem subst_closed (t s : Term) (n : ℕ) (h : isClosed t) :
    subst t n s = t := by
  induction t with
  | f₀ | f₁ | z => rfl
  | var m => simp [isClosed, freeVars] at h
  | comp a b ih₁ ih₂ =>
    simp [isClosed, freeVars] at h
    simp [subst, ih₁ (by exact List.append_eq_nil.mp h |>.1),
                  ih₂ (by exact List.append_eq_nil.mp h |>.2)]
  | obs a ih =>
    simp [subst, ih (by exact h)]
  | oplus a b ih₁ ih₂ =>
    simp [isClosed, freeVars] at h
    simp [subst, ih₁ (by exact List.append_eq_nil.mp h |>.1),
                  ih₂ (by exact List.append_eq_nil.mp h |>.2)]
  | oneg a ih =>
    simp [subst, ih (by exact h)]

/-! ## Part 5: Encoding the Axioms

Each framework axiom can be expressed as a Term equation.
These are the syntactic objects that the Gödel encoding encodes. -/

/-- Formulas: equations between terms, with logical connectives -/
inductive Formula where
  | eq : Term → Term → Formula
  | ne : Term → Term → Formula
  | and : Formula → Formula → Formula
  | or : Formula → Formula → Formula
  | not : Formula → Formula
  | imp : Formula → Formula → Formula
  | forall_ : ℕ → Formula → Formula
  | exists_ : ℕ → Formula → Formula
  deriving Repr, BEq, DecidableEq

namespace Formula

/-- Encode formulas using tag 5+ to avoid collision with Term encoding -/
def encode : Formula → ℕ
  | .eq a b       => Nat.pair 5 (Nat.pair (Term.encode a) (Term.encode b))
  | .ne a b       => Nat.pair 6 (Nat.pair (Term.encode a) (Term.encode b))
  | .and φ ψ      => Nat.pair 7 (Nat.pair (encode φ) (encode ψ))
  | .or φ ψ       => Nat.pair 8 (Nat.pair (encode φ) (encode ψ))
  | .not φ        => Nat.pair 9 (encode φ)
  | .imp φ ψ      => Nat.pair 10 (Nat.pair (encode φ) (encode ψ))
  | .forall_ n φ  => Nat.pair 11 (Nat.pair n (encode φ))
  | .exists_ n φ  => Nat.pair 12 (Nat.pair n (encode φ))

/-- Formula encoding is injective -/
theorem encode_injective : Function.Injective Formula.encode := by
  intro a b h
  induction a with
  | eq a₁ a₂ =>
    cases b <;> simp [Formula.encode, Nat.pair] at h
    case eq b₁ b₂ =>
      have := Nat.pair_injective h
      have h₂ := Nat.pair_injective this.2
      exact congrArg₂ Formula.eq (Term.encode_injective h₂.1) (Term.encode_injective h₂.2)
  | ne a₁ a₂ =>
    cases b <;> simp [Formula.encode, Nat.pair] at h
    case ne b₁ b₂ =>
      have := Nat.pair_injective h
      have h₂ := Nat.pair_injective this.2
      exact congrArg₂ Formula.ne (Term.encode_injective h₂.1) (Term.encode_injective h₂.2)
  | and φ ψ ihφ ihψ =>
    cases b <;> simp [Formula.encode, Nat.pair] at h
    case and φ' ψ' =>
      have := Nat.pair_injective h
      have h₂ := Nat.pair_injective this.2
      exact congrArg₂ Formula.and (ihφ h₂.1) (ihψ h₂.2)
  | or φ ψ ihφ ihψ =>
    cases b <;> simp [Formula.encode, Nat.pair] at h
    case or φ' ψ' =>
      have := Nat.pair_injective h
      have h₂ := Nat.pair_injective this.2
      exact congrArg₂ Formula.or (ihφ h₂.1) (ihψ h₂.2)
  | not φ ihφ =>
    cases b <;> simp [Formula.encode, Nat.pair] at h
    case not φ' =>
      have := Nat.pair_injective h
      exact congrArg Formula.not (ihφ this.2)
  | imp φ ψ ihφ ihψ =>
    cases b <;> simp [Formula.encode, Nat.pair] at h
    case imp φ' ψ' =>
      have := Nat.pair_injective h
      have h₂ := Nat.pair_injective this.2
      exact congrArg₂ Formula.imp (ihφ h₂.1) (ihψ h₂.2)
  | forall_ n φ ihφ =>
    cases b <;> simp [Formula.encode, Nat.pair] at h
    case forall_ m φ' =>
      have := Nat.pair_injective h
      have h₂ := Nat.pair_injective this.2
      exact congrArg₂ Formula.forall_ h₂.1 (ihφ h₂.2)
  | exists_ n φ ihφ =>
    cases b <;> simp [Formula.encode, Nat.pair] at h
    case exists_ m φ' =>
      have := Nat.pair_injective h
      have h₂ := Nat.pair_injective this.2
      exact congrArg₂ Formula.exists_ h₂.1 (ihφ h₂.2)

end Formula

/-! ## Part 6: Axioms as Syntactic Objects

We express each framework axiom as a Formula. These are the
syntactic objects whose Gödel numbers live in the eigenstate orbit.

Convention: var 0 = "x", var 1 = "y", var 2 = "z_var" (to avoid
collision with the constant z). -/

/-- A1: obs(f₁) = f₁ -/
def axiomA1 : Formula :=
  .eq (.obs .f₁) .f₁

/-- A2: ∀x. compose(f₀, x) = x -/
def axiomA2 : Formula :=
  .forall_ 0 (.eq (.comp .f₀ (.var 0)) (.var 0))

/-- A5a: ∀x y z. compose(x, compose(y, z)) = compose(compose(x, y), z) -/
def axiomA5a : Formula :=
  .forall_ 0 (.forall_ 1 (.forall_ 2
    (.eq (.comp (.var 0) (.comp (.var 1) (.var 2)))
         (.comp (.comp (.var 0) (.var 1)) (.var 2)))))

/-- A5b: ∀x y. compose(x, y) = compose(y, x) -/
def axiomA5b : Formula :=
  .forall_ 0 (.forall_ 1
    (.eq (.comp (.var 0) (.var 1)) (.comp (.var 1) (.var 0))))

/-- A6: ∀x. compose(z, x) = z -/
def axiomA6 : Formula :=
  .forall_ 0 (.eq (.comp .z (.var 0)) .z)

/-- A7: ∀x y. compose(f₁, x) = compose(f₁, y) → x = y -/
def axiomA7 : Formula :=
  .forall_ 0 (.forall_ 1
    (.imp (.eq (.comp .f₁ (.var 0)) (.comp .f₁ (.var 1)))
          (.eq (.var 0) (.var 1))))

/-! ### Gödel numbers of axioms

These are concrete natural numbers — each one is simultaneously
the code of an axiom, a natural number, and (in the framework)
an eigenstate. -/

/-- The Gödel number of axiom A1: ⌜obs(f₁) = f₁⌝ -/
def goedelA1 : ℕ := Formula.encode axiomA1

/-- The Gödel number of axiom A2 -/
def goedelA2 : ℕ := Formula.encode axiomA2

/-! ## Part 7: The Triple Identity

This section connects the Gödel encoding to the framework's
eigenstate orbit. Each Gödel number N indexes an eigenstate
f_N = iterS N, giving the triple identity:

  f_N is simultaneously:
    (a) The natural number N (eigenvalue under obs)
    (b) A composable, observable process in State
    (c) The code ⌜T⌝ for some term T in the framework's language

The connection is via iterS: the map Term → State given by
  T ↦ iterS (encode T)
sends each term to "the eigenstate that IS its own code." -/

section TripleIdentity

variable {State : Type*} [SpectralMonoid State] [InfiniteOrbit State]

/-- The Gödel state of a term: the eigenstate indexed by its Gödel number.
    This is the formal expression of "eigenstate f_N where N = ⌜T⌝". -/
def goedelState (t : Term) : State := iterS (encode t)

/-- Different terms map to different eigenstates.
    Follows from injectivity of encode and injectivity of iterS. -/
theorem goedelState_injective : Function.Injective (goedelState (State := State)) :=
  Function.Injective.comp iterS_injective encode_injective

/-- The Gödel state is always a natural number (in the orbit). -/
theorem goedelState_isNat (t : Term) : isNat (goedelState t : State) :=
  ⟨encode t, rfl⟩

/-- The Gödel state of a term is never the annihilator z.
    (Because iterS n ≠ z for the orbit elements — this requires
    that z is not in the natural number orbit.) -/

end TripleIdentity

/-! ## Part 8: Syntactic Predicates on Codes

These are decidable predicates on ℕ that check syntactic properties
of the encoded terms. They correspond to the primitive recursive
predicates in the pen-and-paper theory. -/

/-- Check if a natural number is the Gödel code of a constant -/
def isConstCode (n : ℕ) : Bool :=
  n = Nat.pair 0 0 || n = Nat.pair 0 1 || n = Nat.pair 0 2

/-- Check if a natural number is the Gödel code of a variable -/
def isVarCode (n : ℕ) : Bool :=
  let (tag, val) := Nat.unpair n
  tag == 0 && val >= 3

/-- Check if a natural number is the Gödel code of a leaf (constant or variable) -/
def isLeafCode (n : ℕ) : Bool :=
  let (tag, _) := Nat.unpair n
  tag == 0

/-- Extract the constructor tag from a Gödel code -/
def codeTag (n : ℕ) : ℕ := (Nat.unpair n).1

/-- Extract the payload from a Gödel code -/
def codePayload (n : ℕ) : ℕ := (Nat.unpair n).2

/-- Constants encode to constant codes -/
theorem isConstCode_f₀ : isConstCode (encode .f₀) = true := by
  simp [isConstCode, encode]

theorem isConstCode_f₁ : isConstCode (encode .f₁) = true := by
  simp [isConstCode, encode]

theorem isConstCode_z : isConstCode (encode .z) = true := by
  simp [isConstCode, encode]

/-- Variables encode to variable codes -/
theorem isVarCode_var (n : ℕ) : isVarCode (encode (.var n)) = true := by
  simp [isVarCode, encode, Nat.unpair_pair]
  omega

/-- Compound terms don't encode to leaf codes -/
theorem codeTag_comp (a b : Term) : codeTag (encode (.comp a b)) = 1 := by
  simp [codeTag, encode, Nat.unpair_pair]

theorem codeTag_obs (a : Term) : codeTag (encode (.obs a)) = 2 := by
  simp [codeTag, encode, Nat.unpair_pair]

theorem codeTag_oplus (a b : Term) : codeTag (encode (.oplus a b)) = 3 := by
  simp [codeTag, encode, Nat.unpair_pair]

theorem codeTag_oneg (a : Term) : codeTag (encode (.oneg a)) = 4 := by
  simp [codeTag, encode, Nat.unpair_pair]

end Term

/-! ## Part 9: Axiom Checking Predicate

Given a Gödel number, we can (in principle) check whether it
encodes one of the framework's axioms. This predicate is
decidable because our terms and formulas have DecidableEq. -/

/-- The list of ground axioms (those without quantifiers / not schemas).
    A1 is the only purely ground axiom. -/
def groundAxioms : List Formula :=
  [Term.axiomA1]

/-- Check if a formula code matches axiom A1: obs(f₁) = f₁ -/
def isAxiomA1Code (n : ℕ) : Bool :=
  n == Formula.encode Term.axiomA1

end SpectralMonoid
