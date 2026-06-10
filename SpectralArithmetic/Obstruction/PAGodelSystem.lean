/-
  GodelSystem Instance for Peano Arithmetic
  ==========================================

  Issue #35: instantiate the GodelSystem structure (from Diagonal.lean)
  for Peano arithmetic, discharging the axiomatized fields with concrete
  constructions.

  This is the substantive missing piece in the formalization chain:
    Encoding obstruction (universal) -> GodelSystem (axiomatized)
       -> diagonal lemma -> incompleteness

  Currently the GodelSystem axioms are discharged ABSTRACTLY (any system
  satisfying them gets incompleteness). This file shows that PA SPECIFICALLY
  satisfies them — making the entire chain machine-checked for PA.

  SUPERSEDED FOR THE REAL-PA STORY (2026-06-10): the GodelSystem
  instance for genuine Peano Arithmetic now exists in
  FoundationBridge.paGodelSystemF, built on the Foundation library
  with a real Encodable decode and representability discharged by the
  arithmetic fixed-point theorem — standard Lean axioms only, and our
  diagonal_lemma instantiates as FoundationBridge.pa_diagonal_lemma.
  This file's toy PATerm scaffolding is retained for the Phase 1
  encoding-injectivity content (used by the paper) and as the
  TermF-side worked example; its two remaining axioms are scaffolding
  for the toy model only and are no longer load-bearing for the
  thesis.

  Scope (realistic for one session):

  Phase 1 (PROVED here): PA terms with Godel encoding via prime factorization,
  including injectivity. ~200 lines.

  Phase 2-4 (SCAFFOLDED here, axiomatized for now):
  - Primitive recursive functions including the diagonal function diagN
  - Representability of primitive recursive functions in PA
  - The compose_diag formula and its provability

  Each phase is a separate substantial project. Phase 3 (representability)
  is the deepest — it's the core technical content of Godel's 1931 proof.
  Existing formalizations of representability (Flypitch, etc.) take
  thousands of lines.

  The contribution here: scaffolding that makes the work TRACTABLE.
  Each axiom is a precise mathematical claim with a known classical proof.
  Discharging them is incremental; the structure that needs filling is
  fixed by this file.
-/

import SpectralArithmetic.Obstruction.Diagonal
import SpectralArithmetic.Obstruction.EvalRewrite

set_option linter.style.setOption false
set_option linter.flexible false

namespace PAGodelSystem

open EvalRewrite EvalRewrite.PATerm
abbrev PATerm := EvalRewrite.PATerm

/-! ## Part 1: PA Formulas (a Minimal Variant)

    For the diagonal lemma, we need formulas with one free variable.
    A formula is a syntactic object that, when applied to a numeral,
    gives a sentence (a closed formula).

    For this scaffolding, we use a minimal formula representation:
    a formula is a pair (function, code) where the function takes a
    natural number and returns a sentence (PATerm).

    A more rigorous version would have a full inductive type for
    PA formulas with quantifiers, connectives, etc. We defer this
    to keep Phase 1 tractable. -/

/-- A PA formula with one free variable: a function from numerals
    to sentences. The "free variable" is the natural number argument. -/
structure PAFormula where
  /-- The function: given a numeral n, produce the sentence obtained
      by substituting the numeral for the free variable. -/
  apply : ℕ → PATerm
  /-- The code of this formula (Godel number).
      In a full formalization, this would be derived from a syntactic
      representation; here we make it part of the structure. -/
  code : ℕ

/-! ## Part 2: Godel Encoding via Prime Factorization

    The standard Godel encoding: each PA constructor gets a code,
    each term is encoded as a product of prime powers indexed by the
    constructor codes of its sub-terms.

    For PATerm with 4 constructors (zero, succ, plus, times), we
    use codes 1, 2, 3, 4 and prime powers 2^code at the appropriate
    position. -/

/-- The Godel encoding of a PA term via prime factorization. -/
def encodeTerm : PATerm → ℕ
  | .zero => 1
  | .succ t => 2 ^ (1 + encodeTerm t)
  | .plus a b => 3 ^ (1 + encodeTerm a) * 5 ^ (1 + encodeTerm b)
  | .times a b => 7 ^ (1 + encodeTerm a) * 11 ^ (1 + encodeTerm b)

/-- The encoding is positive (always >= 1). -/
theorem encodeTerm_pos (t : PATerm) : encodeTerm t ≥ 1 := by
  induction t with
  | zero => simp [encodeTerm]
  | succ t _ =>
    simp [encodeTerm]
    exact Nat.one_le_two_pow
  | plus a b iha _ =>
    simp [encodeTerm]
    have h3 : 3 ^ (1 + encodeTerm a) ≥ 1 := Nat.one_le_pow _ _ (by omega)
    have h5 : 5 ^ (1 + encodeTerm b) ≥ 1 := Nat.one_le_pow _ _ (by omega)
    exact Nat.one_le_iff_ne_zero.mpr (by positivity)
  | times a b _ _ =>
    simp [encodeTerm]
    exact Nat.one_le_iff_ne_zero.mpr (by positivity)

/-! ## Part 3: Injectivity

    The Godel encoding is injective: different terms get different codes.
    The proof splits into:
    (a) Cross-constructor: distinguish different constructor types by
        divisibility (`three_not_dvd_pow_two`, `seven_not_dvd_pow_two`,
        `seven_not_dvd_3pow_5pow`, `three_not_dvd_7pow_11pow`).
    (b) Same-constructor: recurse into sub-terms via injectivity of
        `2^·` and the pairing functions `(a,b) ↦ 3^(1+a)·5^(1+b)` and
        `(a,b) ↦ 7^(1+a)·11^(1+b)` (derived from `Nat.factorization`). -/

/-- `encodeTerm .zero = 1`. -/
theorem encodeTerm_zero : encodeTerm .zero = 1 := rfl

/-- The encoding of `.succ t` is at least 4. -/
theorem encodeTerm_succ_ge_four (t : PATerm) : encodeTerm (.succ t) ≥ 4 := by
  change 2 ^ (1 + encodeTerm t) ≥ 4
  have h : encodeTerm t ≥ 1 := encodeTerm_pos t
  have : (2 : ℕ) ^ (1 + encodeTerm t) ≥ 2 ^ 2 := by
    apply Nat.pow_le_pow_right (by omega)
    omega
  simpa using this

/-- The encoding of `.plus a b` is at least `3 * 5 = 15`, hence > 1. -/
theorem encodeTerm_plus_gt_one (a b : PATerm) : encodeTerm (.plus a b) > 1 := by
  change 3 ^ (1 + encodeTerm a) * 5 ^ (1 + encodeTerm b) > 1
  have ha : encodeTerm a ≥ 1 := encodeTerm_pos a
  have hb : encodeTerm b ≥ 1 := encodeTerm_pos b
  have h3 : (3 : ℕ) ^ (1 + encodeTerm a) ≥ 9 := by
    have : (3 : ℕ) ^ (1 + encodeTerm a) ≥ 3 ^ 2 :=
      Nat.pow_le_pow_right (by omega) (by omega)
    simpa using this
  have h5 : (5 : ℕ) ^ (1 + encodeTerm b) ≥ 25 := by
    have : (5 : ℕ) ^ (1 + encodeTerm b) ≥ 5 ^ 2 :=
      Nat.pow_le_pow_right (by omega) (by omega)
    simpa using this
  have : 9 * 25 ≤ 3 ^ (1 + encodeTerm a) * 5 ^ (1 + encodeTerm b) :=
    Nat.mul_le_mul h3 h5
  omega

/-- The encoding of `.times a b` is at least `7 * 11 = 77`, hence > 1. -/
theorem encodeTerm_times_gt_one (a b : PATerm) : encodeTerm (.times a b) > 1 := by
  change 7 ^ (1 + encodeTerm a) * 11 ^ (1 + encodeTerm b) > 1
  have ha : encodeTerm a ≥ 1 := encodeTerm_pos a
  have hb : encodeTerm b ≥ 1 := encodeTerm_pos b
  have h7 : (7 : ℕ) ^ (1 + encodeTerm a) ≥ 49 := by
    have : (7 : ℕ) ^ (1 + encodeTerm a) ≥ 7 ^ 2 :=
      Nat.pow_le_pow_right (by omega) (by omega)
    simpa using this
  have h11 : (11 : ℕ) ^ (1 + encodeTerm b) ≥ 121 := by
    have : (11 : ℕ) ^ (1 + encodeTerm b) ≥ 11 ^ 2 :=
      Nat.pow_le_pow_right (by omega) (by omega)
    simpa using this
  have : 49 * 121 ≤ 7 ^ (1 + encodeTerm a) * 11 ^ (1 + encodeTerm b) :=
    Nat.mul_le_mul h7 h11
  omega

/-- `.zero` is distinguishable from `.succ t`. -/
theorem encodeTerm_zero_ne_succ (t : PATerm) :
    encodeTerm .zero ≠ encodeTerm (.succ t) := by
  rw [encodeTerm_zero]
  have := encodeTerm_succ_ge_four t
  omega

/-- `.zero` is distinguishable from `.plus a b`. -/
theorem encodeTerm_zero_ne_plus (a b : PATerm) :
    encodeTerm .zero ≠ encodeTerm (.plus a b) := by
  rw [encodeTerm_zero]
  have := encodeTerm_plus_gt_one a b
  omega

/-- `.zero` is distinguishable from `.times a b`. -/
theorem encodeTerm_zero_ne_times (a b : PATerm) :
    encodeTerm .zero ≠ encodeTerm (.times a b) := by
  rw [encodeTerm_zero]
  have := encodeTerm_times_gt_one a b
  omega

/-! ### Cross-constructor distinctness by divisibility

    `.succ t` encodes to a power of 2 (so 3 ∤ it).
    `.plus a b` encodes to `3^_ * 5^_` (so 3 ∣ it, 7 ∤ it).
    `.times a b` encodes to `7^_ * 11^_` (so 7 ∣ it, 3 ∤ it).

    Each coprimality fact follows from `Nat.Prime.dvd_of_dvd_pow`. -/

/-- `2^k` is never divisible by 3. -/
theorem three_not_dvd_pow_two (k : ℕ) : ¬ (3 ∣ 2 ^ k) := by
  intro h
  have : (3 : ℕ) ∣ 2 := Nat.prime_three.dvd_of_dvd_pow h
  omega

/-- `2^k` is never divisible by 7. -/
theorem seven_not_dvd_pow_two (k : ℕ) : ¬ (7 ∣ 2 ^ k) := by
  intro h
  have hp : Nat.Prime 7 := by norm_num
  have : (7 : ℕ) ∣ 2 := hp.dvd_of_dvd_pow h
  omega

/-- `3^x * 5^y` is never divisible by 7. -/
theorem seven_not_dvd_3pow_5pow (x y : ℕ) : ¬ (7 ∣ 3 ^ x * 5 ^ y) := by
  intro h
  have hp : Nat.Prime 7 := by norm_num
  rcases hp.dvd_mul.mp h with h1 | h2
  · have : (7 : ℕ) ∣ 3 := hp.dvd_of_dvd_pow h1
    omega
  · have : (7 : ℕ) ∣ 5 := hp.dvd_of_dvd_pow h2
    omega

/-- `7^x * 11^y` is never divisible by 3. -/
theorem three_not_dvd_7pow_11pow (x y : ℕ) : ¬ (3 ∣ 7 ^ x * 11 ^ y) := by
  intro h
  rcases Nat.prime_three.dvd_mul.mp h with h1 | h2
  · have : (3 : ℕ) ∣ 7 := Nat.prime_three.dvd_of_dvd_pow h1
    omega
  · have : (3 : ℕ) ∣ 11 := Nat.prime_three.dvd_of_dvd_pow h2
    omega

/-- 3 divides any `.plus` encoding. -/
theorem three_dvd_encodeTerm_plus (a b : PATerm) :
    (3 : ℕ) ∣ encodeTerm (.plus a b) := by
  change (3 : ℕ) ∣ 3 ^ (1 + encodeTerm a) * 5 ^ (1 + encodeTerm b)
  exact (dvd_pow_self 3 (by omega)).mul_right _

/-- 7 divides any `.times` encoding. -/
theorem seven_dvd_encodeTerm_times (a b : PATerm) :
    (7 : ℕ) ∣ encodeTerm (.times a b) := by
  change (7 : ℕ) ∣ 7 ^ (1 + encodeTerm a) * 11 ^ (1 + encodeTerm b)
  exact (dvd_pow_self 7 (by omega)).mul_right _

/-- `.succ t` ≠ `.plus a b` because one is a power of 2 and the other
    is divisible by 3. -/
theorem encodeTerm_succ_ne_plus (t a b : PATerm) :
    encodeTerm (.succ t) ≠ encodeTerm (.plus a b) := by
  intro h
  have h_plus_div := three_dvd_encodeTerm_plus a b
  rw [← h] at h_plus_div
  exact three_not_dvd_pow_two _ h_plus_div

/-- `.succ t` ≠ `.times a b` — power of 2 vs divisible by 7. -/
theorem encodeTerm_succ_ne_times (t a b : PATerm) :
    encodeTerm (.succ t) ≠ encodeTerm (.times a b) := by
  intro h
  have h_times_div := seven_dvd_encodeTerm_times a b
  rw [← h] at h_times_div
  exact seven_not_dvd_pow_two _ h_times_div

/-- `.plus a b` ≠ `.times c d` — divisible by 3 vs not divisible by 3. -/
theorem encodeTerm_plus_ne_times (a b c d : PATerm) :
    encodeTerm (.plus a b) ≠ encodeTerm (.times c d) := by
  intro h
  have h_plus_div := three_dvd_encodeTerm_plus a b
  rw [h] at h_plus_div
  exact three_not_dvd_7pow_11pow _ _ h_plus_div

/-! ### Same-constructor injectivity

    For terms with the same top-level constructor, we recurse into
    sub-terms. This uses injectivity of `2^·` and of the pairing
    functions `(a,b) ↦ 3^(1+a)·5^(1+b)` and `(a,b) ↦ 7^(1+a)·11^(1+b)`,
    extracted via `Nat.factorization` at the relevant primes. -/

/-- `2^k` is injective in `k`. -/
theorem pow_two_injective : Function.Injective (fun k => 2 ^ k) :=
  Nat.pow_right_injective (by omega)

private lemma pair_factorization_eq
    {p q : ℕ} (hp : p.Prime) (hq : q.Prime) (hpq : p ≠ q) (a b : ℕ) :
    (p ^ (1 + a) * q ^ (1 + b)).factorization p = 1 + a ∧
    (p ^ (1 + a) * q ^ (1 + b)).factorization q = 1 + b := by
  have hpne : p ^ (1 + a) ≠ 0 := pow_ne_zero _ hp.ne_zero
  have hqne : q ^ (1 + b) ≠ 0 := pow_ne_zero _ hq.ne_zero
  refine ⟨?_, ?_⟩
  · rw [Nat.factorization_mul hpne hqne, Finsupp.add_apply,
        hp.factorization_pow, hq.factorization_pow,
        Finsupp.single_apply, Finsupp.single_apply,
        if_pos rfl, if_neg hpq.symm, Nat.add_zero]
  · rw [Nat.factorization_mul hpne hqne, Finsupp.add_apply,
        hp.factorization_pow, hq.factorization_pow,
        Finsupp.single_apply, Finsupp.single_apply,
        if_neg hpq, if_pos rfl, Nat.zero_add]

/-- The pairing `3^(x+1) * 5^(y+1)` is injective. -/
theorem plus_pairing_injective :
    Function.Injective (fun (p : ℕ × ℕ) => 3 ^ (1 + p.1) * 5 ^ (1 + p.2)) := by
  intro ⟨a₁, b₁⟩ ⟨a₂, b₂⟩ h
  dsimp only at h
  have hp3 : Nat.Prime 3 := Nat.prime_three
  have hp5 : Nat.Prime 5 := by norm_num
  have hne : (3 : ℕ) ≠ 5 := by decide
  have e1 := pair_factorization_eq hp3 hp5 hne a₁ b₁
  have e2 := pair_factorization_eq hp3 hp5 hne a₂ b₂
  have ea : 1 + a₁ = 1 + a₂ := by
    have := congrArg (fun n => Nat.factorization n 3) h
    simp only at this
    rw [e1.1, e2.1] at this
    exact this
  have eb : 1 + b₁ = 1 + b₂ := by
    have := congrArg (fun n => Nat.factorization n 5) h
    simp only at this
    rw [e1.2, e2.2] at this
    exact this
  have : a₁ = a₂ := by omega
  have : b₁ = b₂ := by omega
  subst ‹a₁ = a₂›; subst ‹b₁ = b₂›; rfl

/-- The pairing `7^(x+1) * 11^(y+1)` is injective. -/
theorem times_pairing_injective :
    Function.Injective (fun (p : ℕ × ℕ) => 7 ^ (1 + p.1) * 11 ^ (1 + p.2)) := by
  intro ⟨a₁, b₁⟩ ⟨a₂, b₂⟩ h
  dsimp only at h
  have hp7 : Nat.Prime 7 := by norm_num
  have hp11 : Nat.Prime 11 := by norm_num
  have hne : (7 : ℕ) ≠ 11 := by decide
  have e1 := pair_factorization_eq hp7 hp11 hne a₁ b₁
  have e2 := pair_factorization_eq hp7 hp11 hne a₂ b₂
  have ea : 1 + a₁ = 1 + a₂ := by
    have := congrArg (fun n => Nat.factorization n 7) h
    simp only at this
    rw [e1.1, e2.1] at this
    exact this
  have eb : 1 + b₁ = 1 + b₂ := by
    have := congrArg (fun n => Nat.factorization n 11) h
    simp only at this
    rw [e1.2, e2.2] at this
    exact this
  have : a₁ = a₂ := by omega
  have : b₁ = b₂ := by omega
  subst ‹a₁ = a₂›; subst ‹b₁ = b₂›; rfl

/-- **Godel encoding injectivity:** distinct PA terms get distinct Godel
    codes. Proof combines cross-constructor distinguishing (via prime
    divisibility) with same-constructor recursion (via injectivity of
    `2^·` and the prime pairings) and structural induction on terms. -/
theorem encodeTerm_injective : Function.Injective encodeTerm := by
  intro t1 t2 h
  induction t1 generalizing t2 with
  | zero =>
    cases t2 with
    | zero => rfl
    | succ t => exact absurd h (encodeTerm_zero_ne_succ t)
    | plus a b => exact absurd h (encodeTerm_zero_ne_plus a b)
    | times a b => exact absurd h (encodeTerm_zero_ne_times a b)
  | succ t1 ih =>
    cases t2 with
    | zero => exact absurd h.symm (encodeTerm_zero_ne_succ t1)
    | succ t2 =>
      -- 2^(1 + encode t1) = 2^(1 + encode t2)
      have : 1 + encodeTerm t1 = 1 + encodeTerm t2 :=
        pow_two_injective h
      have : encodeTerm t1 = encodeTerm t2 := by omega
      rw [ih this]
    | plus a b => exact absurd h (encodeTerm_succ_ne_plus t1 a b)
    | times a b => exact absurd h (encodeTerm_succ_ne_times t1 a b)
  | plus a b iha ihb =>
    cases t2 with
    | zero => exact absurd h.symm (encodeTerm_zero_ne_plus a b)
    | succ t => exact absurd h.symm (encodeTerm_succ_ne_plus t a b)
    | plus c d =>
      have heq : (encodeTerm a, encodeTerm b) = (encodeTerm c, encodeTerm d) :=
        plus_pairing_injective h
      have ha : encodeTerm a = encodeTerm c := (Prod.mk.inj heq).1
      have hb : encodeTerm b = encodeTerm d := (Prod.mk.inj heq).2
      rw [iha ha, ihb hb]
    | times c d => exact absurd h (encodeTerm_plus_ne_times a b c d)
  | times a b iha ihb =>
    cases t2 with
    | zero => exact absurd h.symm (encodeTerm_zero_ne_times a b)
    | succ t => exact absurd h.symm (encodeTerm_succ_ne_times t a b)
    | plus c d => exact absurd h.symm (encodeTerm_plus_ne_times c d a b)
    | times c d =>
      have heq : (encodeTerm a, encodeTerm b) = (encodeTerm c, encodeTerm d) :=
        times_pairing_injective h
      have ha : encodeTerm a = encodeTerm c := (Prod.mk.inj heq).1
      have hb : encodeTerm b = encodeTerm d := (Prod.mk.inj heq).2
      rw [iha ha, ihb hb]

/-! ## Part 4: Decoding (Phase 2 Hook)

    Given a code, recover the formula. For the GodelSystem structure,
    we need a left-inverse `decode : ℕ -> Formula` such that
    `decode (code phi) = phi`.

    That property cannot hold on ALL of PAFormula: `code` is a free
    field, so two formulas can share a code while differing in
    `apply`, and no function inverts a non-injective one. (An earlier
    version asserted exactly that of a stub decode, which made the
    axiom set inconsistent.)

    The consistent formulation: keep decode opaque, constrained only
    by code preservation, and take the GodelSystem's Formula type to
    be the subtype of decode-canonical formulas — those fixed by the
    decode-of-code round trip. On that subtype, `code` is injective
    and `decode_fcode` is a theorem. Phase 2's job is to provide a
    decode rich enough that the subtype contains one canonical
    formula per syntactic PA formula. -/

instance : Inhabited PAFormula := ⟨⟨fun _ => .zero, 0⟩⟩

/-- A decoding function: given a code, produce a formula.
    Opaque — Phase 2 supplies the real construction (inverting a
    syntactic coding). -/
opaque decodeFormula : ℕ → PAFormula

/-- **DECODE PRESERVES THE CODE (axiomatized — Phase 2):**
    The decoded formula carries the code it was decoded from.
    Satisfiable: any function returning a formula with the given
    code field witnesses it. -/
axiom decodeFormula_code (n : ℕ) : (decodeFormula n).code = n

/-- The canonical (coded) formulas: those fixed by the
    decode-of-code round trip. The GodelSystem instance lives here. -/
def CodedFormula : Type := {φ : PAFormula // decodeFormula φ.code = φ}

/-- Decoding lands in CodedFormula, because decode is idempotent
    through `code` (by `decodeFormula_code`). -/
def decodeCoded (n : ℕ) : CodedFormula :=
  ⟨decodeFormula n, by rw [decodeFormula_code]⟩

instance : Inhabited CodedFormula := ⟨decodeCoded 0⟩

/-! ## Part 5: The Diagonal Function

    diagN(n) = code of the sentence obtained by applying formula-with-code-n
    to the numeral n.

    diagN(n) = scode (subst (decode n) n)
            = scode ((decode n).apply n)

    where scode is the encoding of sentences (which are PATerms). -/

/-- The diagonal function on natural numbers. -/
noncomputable def diagN (n : ℕ) : ℕ := encodeTerm ((decodeFormula n).apply n)

/-- diagN spec by definition. -/
theorem diagN_spec (n : ℕ) :
    diagN n = encodeTerm ((decodeFormula n).apply n) := rfl

/-! ## Part 6: Representability of diagN (Phase 3 — AXIOMATIZED)

    The hard mathematical content: any primitive recursive function
    is representable by a PA formula. diagN is primitive recursive
    (it's a finite combination of arithmetic operations on encoded data).

    In a full formalization, we would:
    1. Define the class of primitive recursive functions
    2. Define what it means for a formula to "represent" a function
    3. Prove that all PR functions are representable

    This is the deepest part of Godel's 1931 paper. We axiomatize it. -/

/-- **REPRESENTABILITY OF diagN (axiomatized — Phase 3):**
    For any base formula beta, there exists a "composed" formula
    (informally: beta ∘ diagN) whose application is provably equivalent
    to applying beta to diagN(n).

    In PA: given beta(x), construct delta(x) = beta(diagN(x)) using
    the representation of diagN. Then PA proves
      subst(delta, n) <-> subst(beta, diagN(n))
    for every numeral n. -/
opaque compose_diag : CodedFormula → CodedFormula

/-- The composed formula's apply implements composition with diagN
    (axiomatized — Phase 3). Satisfiable: with the all-zero decode
    interpretation, every CodedFormula has constant-zero apply and
    the identity witnesses compose_diag. -/
axiom compose_diag_apply (β : CodedFormula) (n : ℕ) :
    (compose_diag β).val.apply n = β.val.apply (diagN n)

/-! ## Part 7: PA's Provability (Phase 4 — Stub)

    For the GodelSystem instance, we need a `provable` predicate.
    For PA, this is: there exists a derivation in PA's deductive system.

    A full formalization requires defining PA's axioms and inference
    rules, then defining `provable` as "derivable from axioms."
    This is substantial but well-understood (Flypitch has it).

    For this scaffolding, we use a placeholder. -/

instance : Inhabited PATerm := ⟨.zero⟩

/-- **PA PROVABILITY (opaque — Phase 4):**
    The provability predicate for PA. In a full formalization, this
    would be defined as derivability from PA's axioms. Opaque data,
    not an axiom: nothing is assumed about it here. -/
opaque paProvable : PATerm → Prop

/-- **PA NEGATION (opaque — Phase 4):**
    Syntactic negation in PA. For the minimal PATerm language,
    we extend with a negation operator (or encode negation as
    "equals zero"). -/
opaque paNeg : PATerm → PATerm

/-! ## Part 8: Toward the GodelSystem Instance — Required Lemmas

    The full GodelSystem instance for PA requires SIX components, of
    which Phase 1 (this file) provides the SCAFFOLDING:

    | Field | Status | What's needed |
    |-------|--------|---------------|
    | provable | Opaque (paProvable) | Phase 4: PA deductive system |
    | neg | Opaque (paNeg) | Phase 4: extend PATerm with negation |
    | Formula | Provided (CodedFormula) | Phase 2: make the subtype rich |
    | subst | Provided (.val.apply) | Enriched in Phase 2 |
    | scode | PROVED (encodeTerm) | Phase 1 ✓ |
    | fcode | Provided (.val.code) | Phase 2: derive from syntax |
    | decode | Opaque (decodeFormula) + decodeFormula_code axiom | Phase 2: full inverse |
    | decode_fcode | PROVED on CodedFormula (decodeCoded_code_val) | — |
    | diagN | PROVED (uses encodeTerm) | Phase 1 ✓ |
    | diagN_spec | PROVED (by definition) | Phase 1 ✓ |
    | compose_diag | Opaque + compose_diag_apply axiom | Phase 3: representability |
    | compose_diag_prov | PROVED (from compose_diag_apply) | — |
    | compose_diag_neg | PROVED (from compose_diag_apply) | — |

    Rather than constructing a paGodelSystem with sorries (which would
    be dishonest), we provide:
    - Phase 1 results as theorems (sorry-free)
    - Phase 2-3 hooks as opaque data plus two satisfiable axioms
      (decodeFormula_code, compose_diag_apply)
    - A precise statement of what FULL DISCHARGE requires

    This is honest about the state: Phase 1 is done, Phases 2-4 are
    the substantial work that remains. The opaque/axiom split keeps
    the assumptions auditable: data that is merely unspecified is
    opaque; only genuine propositions are axioms, and each is
    satisfiable (the all-zero stub decode interprets them all). -/

/-- decode is a left inverse of fcode on CodedFormula — a THEOREM,
    by definition of the subtype. (The earlier phase2_decode_inverse
    axiom asserted this for all PAFormulas, where `code` is not
    injective; that statement was refutable. Restricting Formula to
    CodedFormula is what makes it true.) -/
theorem decodeCoded_code_val (φ : CodedFormula) :
    decodeCoded φ.val.code = φ :=
  Subtype.ext φ.property

/-- The Phase 3 provability equivalence, now a theorem: it follows
    from compose_diag_apply. (Previously a separate axiom, which was
    redundant.) The substantive Phase 3 work is constructing
    compose_diag syntactically and proving compose_diag_apply for it. -/
theorem compose_diag_provable (β : CodedFormula) (n : ℕ) :
    paProvable ((compose_diag β).val.apply n) ↔
    paProvable (β.val.apply (diagN n)) := by
  rw [compose_diag_apply]

/-- Same equivalence under negation; same status. -/
theorem compose_diag_neg_provable (β : CodedFormula) (n : ℕ) :
    paProvable (paNeg ((compose_diag β).val.apply n)) ↔
    paProvable (paNeg (β.val.apply (diagN n))) := by
  rw [compose_diag_apply]

/-- **THE INSTANCE (given the Phase 2-4 axioms and opaque data):**
    The GodelSystem instance for PA over the canonical formulas —
    no sorries needed.

    This shows the framework is COMPLETE modulo the axiomatized
    phases. Discharging them (Phases 2-4) is the remaining work. -/
noncomputable def paGodelSystem : Diagonal.GodelSystem PATerm where
  provable := paProvable
  neg := paNeg
  Formula := CodedFormula
  subst := fun φ n => φ.val.apply n
  scode := encodeTerm
  fcode := fun φ => φ.val.code
  decode := decodeCoded
  decode_fcode := decodeCoded_code_val
  diagN := diagN
  diagN_spec := fun _ => rfl
  compose_diag := compose_diag
  compose_diag_prov := fun β => compose_diag_provable β _
  compose_diag_neg := fun β => compose_diag_neg_provable β _

/-! ## Part 9: Status and What Remains

    PROVED (sorry-free in this file):

    | Item | Content |
    |------|---------|
    | encodeTerm | Godel encoding of PA terms via prime factorization |
    | encodeTerm_pos | Encoding is positive |
    | three_not_dvd_pow_two, seven_not_dvd_pow_two | Prime non-divisibility |
    | seven_not_dvd_3pow_5pow, three_not_dvd_7pow_11pow | Cross-prime non-divisibility |
    | pow_two_injective | 2^· is injective |
    | plus_pairing_injective, times_pairing_injective | Pairing injectivity via Nat.factorization |
    | encodeTerm_injective | Distinct terms get distinct codes |
    | diagN | Diagonal function definition |
    | diagN_spec | diagN computes self-substitution code |
    | decodeCoded_code_val | decode inverts fcode on CodedFormula |
    | compose_diag_provable (+ neg) | Diagonal equivalences from compose_diag_apply |

    OPAQUE DATA (unspecified, nothing assumed beyond the axioms below):

    | Constant | What it is | Phase |
    |----------|------------|-------|
    | decodeFormula | Decoding function | Phase 2 |
    | compose_diag | Composition with the diagonal | Phase 3 |
    | paProvable | Provability predicate for PA | Phase 4 |
    | paNeg | Negation in PA | Phase 4 |

    AXIOMATIZED (Phases 2-3 — incremental work to discharge; each is
    satisfiable, jointly witnessed by the all-zero stub decode):

    | Axiom | What it asserts | Phase |
    |-------|-----------------|-------|
    | decodeFormula_code | Decoding preserves the code | Phase 2 |
    | compose_diag_apply | The diagonal representation works | Phase 3 (deep) |

    INCREMENTAL ROADMAP:

    Phase 1 (DONE): Godel encoding + injectivity from prime factorization.

    Phase 2 (~2 weeks): Define primitive recursive functions in Lean,
    show diagN is PR.

    Phase 3 (~1-2 months): Formalize representability of PR functions
    in PA. This is the deepest part.

    Phase 4 (~2 weeks): Formalize PA's deductive system (axioms,
    rules of inference, derivability).

    Total: ~2-3 months of formalization work remaining (Phases 2-4).

    The current file establishes the SCAFFOLDING — the structure is
    fixed, the axioms are precise, and the work is now incremental
    rather than open-ended.
-/

end PAGodelSystem
