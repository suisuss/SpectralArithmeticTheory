/-
  Quotation Cost: The Tier 3 Growth-Rate Separation
  ==================================================

  Tier 3 of the bisimulation program (Bisimulation.lean proved
  Tiers 1-2). The theory docs conjectured (encoding-obstruction.md,
  Part 5): for ANY primitive recursive injection ε, the semantic
  dynamics and the code dynamics are not bisimilar, via a growth-rate
  argument. Two findings, one negative, one positive:

  NEGATIVE (a correction to the conjecture as sketched): Step 3 of
  the sketch — "codes along the observation trajectory grow with
  term size" — does not follow from injectivity. A single computable
  trajectory is a sparse set, and a non-compositional primitive
  recursive injection can compress it (send the j-th iterate to j,
  everything else high). The conjecture needs a compositionality
  hypothesis; without it the growth argument has a hole. This file
  therefore proves the COMPOSITIONAL version, which is what the
  sketch's Step 1 ("pairing function lower bound") implicitly
  assumed all along.

  POSITIVE (proved here, sorry-free, no axioms): along the canonical
  observation trajectory t₀ = f₂, t_{j+1} = synStep t_j,

  1. CLOSED FORM: t_{2m} = dup^m(f₂) where dup a = oplus(obs a, obs a).
     The even iterates are exact duplication towers.
  2. SYNTACTIC GROWTH: the f₁-leaf count of t_{2m} is exactly 2^(m+1),
     so for every compositional coding (leaf codes ≥ 2 at f₁, pairing
     bounded below by the product — satisfied by standard Godel
     codings), code(t_{2m}) ≥ 2^(2^(m+1)): DOUBLY exponential.
  3. SEMANTIC CONTENT: eval(t_j) = 2^j · f₂ (the eigenvalue
     coefficient), SINGLY exponential — j+1 bits of information.
  4. THE SEPARATION (quotation_overhead_superpolynomial): no
     polynomial relates the code trajectory to the semantic value.
     For every a, d there is a stage where the code exceeds
     a · (semantic value)^d.

  Reading: the quantitative companion to Tier 2. Tier 2 said
  intensional observables support no bisimulation at all; Tier 3
  says even the EXTENSIONAL content carried by a faithful
  compositional code is buried under super-polynomial syntactic
  overhead. Quotation is behaviorally free (codeBisim) but
  quantitatively ruinous: the code tracks the form, the form grows
  doubly exponentially, the meaning grows singly.
-/

import SpectralArithmetic.Obstruction.Bisimulation
import Mathlib.Data.Nat.Pairing

namespace SpectralMonoid

open Term

/-! ## Part 1: The Canonical Observation Trajectory -/

/-- The canonical trajectory: start at f₂ = compose(f₁, f₁) and apply
    the syntactic observation step. -/
def trajectory : ℕ → Term
  | 0 => t_f₂
  | j + 1 => synStep (trajectory j)

/-- Duplication: the shape the trajectory settles into.
    dup(a) = oplus(obs a, obs a). -/
def dup (a : Term) : Term := .oplus (.obs a) (.obs a)

/-- Iterated duplication. -/
def dupIter : ℕ → Term → Term
  | 0, t => t
  | m + 1, t => dup (dupIter m t)

/-- The syntactic step commutes with duplication: stepping a
    duplicated term duplicates the stepped term. -/
theorem synStep_dup (a : Term) : synStep (dup a) = dup (synStep a) := by
  simp only [synStep, dup, deepRewrite, obsRewrite]

/-- Two steps from the seed produce one duplication. -/
theorem trajectory_two : trajectory 2 = dup t_f₂ := by decide

/-- Two steps applied to a duplication tower add one layer. -/
theorem synStep_synStep_dupIter (m : ℕ) :
    synStep (synStep (dupIter m t_f₂)) = dup (dupIter m t_f₂) := by
  induction m with
  | zero =>
    have h := trajectory_two
    simpa [trajectory, dupIter] using h
  | succ m ih =>
    simp only [dupIter, synStep_dup, ih]

/-- **CLOSED FORM:** the even trajectory points are exactly the
    duplication towers over f₂. -/
theorem trajectory_even (m : ℕ) : trajectory (2 * m) = dupIter m t_f₂ := by
  induction m with
  | zero => rfl
  | succ m ih =>
    have h2 : 2 * (m + 1) = (2 * m) + 1 + 1 := by ring
    rw [h2]
    simp only [trajectory, ih]
    exact synStep_synStep_dupIter m

/-! ## Part 2: Syntactic Growth — the f₁-Leaf Count -/

/-- Count of f₁ leaves in a term. The Leibniz rewrite duplicates
    sub-terms, so this count grows along the trajectory; it is the
    size measure a compositional code cannot avoid paying for. -/
def f₁count : Term → ℕ
  | .f₀ => 0
  | .f₁ => 1
  | .z => 0
  | .compose a b => f₁count a + f₁count b
  | .oplus a b => f₁count a + f₁count b
  | .obs a => f₁count a

/-- Duplication doubles the f₁ count. -/
theorem f₁count_dup (a : Term) : f₁count (dup a) = 2 * f₁count a := by
  simp only [dup, f₁count]
  ring

/-- The duplication tower has f₁ count 2^m times the seed's. -/
theorem f₁count_dupIter (m : ℕ) (t : Term) :
    f₁count (dupIter m t) = 2 ^ m * f₁count t := by
  induction m with
  | zero => simp [dupIter]
  | succ m ih =>
    simp only [dupIter, f₁count_dup, ih]
    ring

/-- **SYNTACTIC GROWTH:** the even trajectory points have f₁ count
    exactly 2^(m+1). -/
theorem f₁count_trajectory (m : ℕ) :
    f₁count (trajectory (2 * m)) = 2 ^ (m + 1) := by
  rw [trajectory_even, f₁count_dupIter]
  simp [t_f₂, f₁count]
  ring

/-! ## Part 3: Compositional Codings

    A coding is compositional if it is computed bottom-up: leaf codes
    for the constants, a pairing for each binary constructor, a unary
    map for obs. The lower bounds (pairing dominates the product,
    obs-map does not shrink, f₁'s code is at least 2) are satisfied
    by every standard Godel coding — prime-power codings, Cantor
    pairing towers, the encodeTerm of PAGodelSystem.lean. They are
    exactly what the conjecture's "pairing function lower bound"
    step assumed. Injectivity is NOT assumed: the cost theorem needs
    only compositionality. -/

/-- A compositional coding of terms with the standard growth floors. -/
structure CompositionalCoding where
  /-- Code of f₀. -/
  cF₀ : ℕ
  /-- Code of f₁. -/
  cF₁ : ℕ
  /-- Code of z. -/
  cZ : ℕ
  /-- Pairing for compose nodes. -/
  pairC : ℕ → ℕ → ℕ
  /-- Pairing for oplus nodes. -/
  pairO : ℕ → ℕ → ℕ
  /-- Code map for obs nodes. -/
  unObs : ℕ → ℕ
  /-- Leaf codes are positive. -/
  one_le_cF₀ : 1 ≤ cF₀
  /-- f₁'s code is at least 2 (any injective coding of the three
      distinct leaves has a leaf with code ≥ 2; we pin it at f₁). -/
  two_le_cF₁ : 2 ≤ cF₁
  /-- Leaf codes are positive. -/
  one_le_cZ : 1 ≤ cZ
  /-- The compose pairing dominates the product. -/
  pairC_ge : ∀ a b, a * b ≤ pairC a b
  /-- The oplus pairing dominates the product. -/
  pairO_ge : ∀ a b, a * b ≤ pairO a b
  /-- The obs map does not shrink codes. -/
  unObs_ge : ∀ a, a ≤ unObs a

namespace CompositionalCoding

/-- The bottom-up code of a term. -/
def encode (c : CompositionalCoding) : Term → ℕ
  | .f₀ => c.cF₀
  | .f₁ => c.cF₁
  | .z => c.cZ
  | .compose a b => c.pairC (c.encode a) (c.encode b)
  | .oplus a b => c.pairO (c.encode a) (c.encode b)
  | .obs a => c.unObs (c.encode a)

/-- **THE CODE PAYS FOR EVERY f₁ LEAF:** a compositional code is at
    least 2 to the f₁ count. -/
theorem two_pow_f₁count_le_encode (c : CompositionalCoding) (t : Term) :
    2 ^ f₁count t ≤ c.encode t := by
  induction t with
  | f₀ => simpa [f₁count, encode] using c.one_le_cF₀
  | f₁ => simpa [f₁count, encode] using c.two_le_cF₁
  | z => simpa [f₁count, encode] using c.one_le_cZ
  | compose a b iha ihb =>
    calc 2 ^ f₁count (.compose a b)
        = 2 ^ f₁count a * 2 ^ f₁count b := by simp [f₁count, pow_add]
      _ ≤ c.encode a * c.encode b := Nat.mul_le_mul iha ihb
      _ ≤ c.pairC (c.encode a) (c.encode b) := c.pairC_ge _ _
      _ = c.encode (.compose a b) := rfl
  | oplus a b iha ihb =>
    calc 2 ^ f₁count (.oplus a b)
        = 2 ^ f₁count a * 2 ^ f₁count b := by simp [f₁count, pow_add]
      _ ≤ c.encode a * c.encode b := Nat.mul_le_mul iha ihb
      _ ≤ c.pairO (c.encode a) (c.encode b) := c.pairO_ge _ _
      _ = c.encode (.oplus a b) := rfl
  | obs a iha =>
    calc 2 ^ f₁count (.obs a) = 2 ^ f₁count a := rfl
      _ ≤ c.encode a := iha
      _ ≤ c.unObs (c.encode a) := c.unObs_ge _
      _ = c.encode (.obs a) := rfl

/-- **DOUBLY EXPONENTIAL CODES:** along the canonical trajectory,
    every compositional code is at least 2^(2^(m+1)) at stage 2m. -/
theorem encode_trajectory_ge (c : CompositionalCoding) (m : ℕ) :
    2 ^ 2 ^ (m + 1) ≤ c.encode (trajectory (2 * m)) := by
  have h := c.two_pow_f₁count_le_encode (trajectory (2 * m))
  rwa [f₁count_trajectory] at h

end CompositionalCoding

/-- The compositional class is inhabited: the prime-power coding
    pairC(a,b) = 2^a * 3^b, pairO(a,b) = 5^a * 7^b, unObs(a) = 11^a
    satisfies all the floors. -/
def primePowerCoding : CompositionalCoding where
  cF₀ := 1
  cF₁ := 2
  cZ := 3
  pairC a b := 2 ^ a * 3 ^ b
  pairO a b := 5 ^ a * 7 ^ b
  unObs a := 11 ^ a
  one_le_cF₀ := le_refl 1
  two_le_cF₁ := le_refl 2
  one_le_cZ := by omega
  pairC_ge a b :=
    Nat.mul_le_mul (Nat.le_of_lt (Nat.lt_two_pow_self))
      (Nat.le_of_lt (Nat.lt_pow_self (by omega)))
  pairO_ge a b :=
    Nat.mul_le_mul (Nat.le_of_lt (Nat.lt_pow_self (by omega)))
      (Nat.le_of_lt (Nat.lt_pow_self (by omega)))
  unObs_ge a := Nat.le_of_lt (Nat.lt_pow_self (by omega))

/-! ## Part 4: Semantic Content — Singly Exponential

    The semantic side of the same trajectory: eval(t_j) = 2^j · f₂.
    Each observation multiplies the coefficient by the eigenvalue 2.
    The meaning at stage j is the number 2^j — j+1 bits. -/

/-- obs is linear over the framework's scalar multiple. -/
theorem obs_smul {State : Type*} [DynSemiring State] (n : ℕ) (x : State) :
    obs (DynSemiring.smul n x) = DynSemiring.smul n (obs x) := by
  induction n with
  | zero => exact DynSemiring.obs_z
  | succ n ih =>
    rw [DynSemiring.smul_succ, DynSemiring.obs_oplus, ih,
      DynSemiring.smul_succ]

/-- Scalar multiples compose additively. -/
theorem smul_add {State : Type*} [DynSemiring State] (p q : ℕ) (x : State) :
    DynSemiring.smul (p + q) x =
      DynSemiring.oplus (DynSemiring.smul p x) (DynSemiring.smul q x) := by
  induction p with
  | zero => simp
  | succ p ih =>
    rw [Nat.succ_add, DynSemiring.smul_succ, DynSemiring.smul_succ, ih,
      DynSemiring.oplus_assoc]

/-- Scalar multiples compose multiplicatively. -/
theorem smul_smul {State : Type*} [DynSemiring State] (p q : ℕ) (x : State) :
    DynSemiring.smul p (DynSemiring.smul q x) =
      DynSemiring.smul (p * q) x := by
  induction p with
  | zero => simp
  | succ p ih =>
    rw [DynSemiring.smul_succ, ih, Nat.succ_mul, Nat.add_comm, smul_add]

/-- One scalar copy is the state itself. -/
theorem smul_one {State : Type*} [DynSemiring State] (x : State) :
    DynSemiring.smul 1 x = x := by
  have h : DynSemiring.smul 1 x = DynSemiring.oplus x (z : State) := rfl
  rw [h, DynSemiring.oplus_comm, DynSemiring.oplus_z]

/-- Observing f₂ doubles it: the eigenvalue at the seed is 2. -/
theorem obs_eval_t_f₂ {State : Type*} [DynSemiring State] :
    obs (eval t_f₂ : State) = DynSemiring.smul 2 (eval t_f₂) := by
  have h2 : DynSemiring.smul 2 (eval t_f₂ : State) =
      DynSemiring.oplus (eval t_f₂) (eval t_f₂) := by
    calc DynSemiring.smul 2 (eval t_f₂ : State)
        = DynSemiring.oplus (eval t_f₂) (DynSemiring.smul 1 (eval t_f₂)) :=
          rfl
      _ = DynSemiring.oplus (eval t_f₂) (eval t_f₂) := by rw [smul_one]
  rw [h2]
  change obs (compose (eval .f₁) (eval .f₁) : State) = _
  rw [DynSemiring.leibniz]
  have hf₁ : obs (eval .f₁ : State) = eval .f₁ := obs_f₁
  rw [hf₁]
  rfl

/-- **SEMANTIC CONTENT:** the trajectory evaluates to 2^j · f₂.
    The j-th observation of f₂ carries exactly the number 2^j. -/
theorem eval_trajectory {State : Type*} [DynSemiring State] (j : ℕ) :
    eval (trajectory j) = DynSemiring.smul (2 ^ j) (eval t_f₂ : State) := by
  induction j with
  | zero => rw [pow_zero, smul_one]; rfl
  | succ j ih =>
    change eval (synStep (trajectory j)) = _
    rw [synStep_eval, ih, obs_smul, obs_eval_t_f₂, smul_smul,
      pow_succ]

/-! ## Part 5: The Separation -/

private theorem lt_two_pow_self' (n : ℕ) : n < 2 ^ n := by
  induction n with
  | zero => simp
  | succ k ih =>
    have h1 : (1 : ℕ) ≤ 2 ^ k := Nat.one_le_two_pow
    have h2 : 2 ^ (k + 1) = 2 ^ k + 2 ^ k := by ring
    omega

private theorem sq_lin_lt_two_pow (k : ℕ) :
    ∀ m, k + 1 ≤ m → k * m < 2 ^ m := by
  intro m
  induction m with
  | zero => omega
  | succ p ih =>
    intro hkp
    rcases Nat.lt_or_ge (k + 1) (p + 1) with hlt | hge
    · have hkp' : k + 1 ≤ p := by omega
      have h1 : k * p < 2 ^ p := ih hkp'
      have h2 : k < 2 ^ p := by
        have := lt_two_pow_self' k
        have hpow : 2 ^ k ≤ 2 ^ p := Nat.pow_le_pow_right (by omega) (by omega)
        omega
      have h3 : 2 ^ (p + 1) = 2 ^ p + 2 ^ p := by ring
      have : k * (p + 1) = k * p + k := by ring
      omega
    · have hk : k = p := by omega
      subst hk
      clear ih hkp hge
      induction k with
      | zero => simp
      | succ q ihq =>
        have hq : q * (q + 1) < 2 ^ (q + 1) := ihq
        have hq2 : q + 1 ≤ 2 ^ q := lt_two_pow_self' q
        have h3 : 2 ^ (q + 1 + 1) = 2 ^ (q + 1) + 2 ^ (q + 1) := by ring
        have h4 : 2 ^ (q + 1) = 2 ^ q + 2 ^ q := by ring
        have h5 : (q + 1) * (q + 1 + 1) = q * (q + 1) + 2 * (q + 1) := by
          ring
        omega

/-- **QUOTATION OVERHEAD IS SUPER-POLYNOMIAL (Tier 3, compositional):**
    along the canonical observation trajectory, no polynomial in the
    semantic value bounds the code. For every coefficient a and degree
    d there is a stage 2m where the code of the term exceeds
    a · (2^(2m))^d — and 2^(2m) is precisely the semantic content at
    that stage (eval_trajectory). The code is doubly exponential, the
    meaning singly: quotation is behaviorally free (codeBisim) but
    carries unavoidable super-polynomial syntactic debt. -/
theorem quotation_overhead_superpolynomial (c : CompositionalCoding)
    (a d : ℕ) :
    ∃ m : ℕ, a * (2 ^ (2 * m)) ^ d < c.encode (trajectory (2 * m)) := by
  refine ⟨a + 2 * d, ?_⟩
  set m := a + 2 * d with hm
  have hcode := c.encode_trajectory_ge m
  have key : a * (2 ^ (2 * m)) ^ d < 2 ^ 2 ^ (m + 1) := by
    have ha : a ≤ 2 ^ a := Nat.le_of_lt (lt_two_pow_self' a)
    have hexp : a + 2 * m * d < 2 ^ (m + 1) := by
      have hlin : a + 2 * m * d ≤ (a + 2 * d) * (m + 1) := by nlinarith
      have hsq : (a + 2 * d) * (m + 1) < 2 ^ (m + 1) :=
        sq_lin_lt_two_pow (a + 2 * d) (m + 1) (by omega)
      omega
    calc a * (2 ^ (2 * m)) ^ d
        ≤ 2 ^ a * (2 ^ (2 * m)) ^ d := Nat.mul_le_mul_right _ ha
      _ = 2 ^ (a + 2 * m * d) := by rw [← pow_mul, ← pow_add]
      _ < 2 ^ 2 ^ (m + 1) :=
          Nat.pow_lt_pow_right (by omega) hexp
  exact Nat.lt_of_lt_of_le key hcode

/-! ## Part 6: Summary

    PROVED (sorry-free, no axioms):

    | Theorem | Content |
    |---------|---------|
    | trajectory_even | t_{2m} = dup^m(f₂) — exact closed form |
    | f₁count_trajectory | f₁ count at stage 2m is exactly 2^(m+1) |
    | two_pow_f₁count_le_encode | Compositional codes pay 2^(f₁ count) |
    | encode_trajectory_ge | Codes along the trajectory ≥ 2^(2^(m+1)) |
    | primePowerCoding | The compositional class is inhabited |
    | eval_trajectory | Semantic content at stage j is exactly 2^j |
    | quotation_overhead_superpolynomial | No polynomial in the semantic value bounds the code |

    WHAT THIS SETTLES AND WHAT IT DOES NOT:

    Settled: the growth-rate separation conjectured in
    encoding-obstruction.md Part 5, for the class of compositional
    codings — which is the class its own proof sketch (Step 1,
    pairing lower bounds) implicitly assumed.

    Corrected: the conjecture's quantification over ALL primitive
    recursive injections is too strong for the sketched argument:
    injectivity alone does not force code growth along a fixed
    computable trajectory (sparse-set compression). Any future
    strengthening must either add compositionality (done here),
    or find a genuinely different argument.

    Open: a bisimulation-flavored statement on a common carrier for
    non-compositional codings, and the connection between this cost
    gap and proof-length lower bounds (issues #33, #38). -/

/-! ## Part 7: Necessity of Compositionality — the Non-Compositional
    Case Refuted

    The original conjecture quantified over ALL primitive recursive
    injections. This part refutes that quantification in its only
    precise quantitative reading: there EXISTS an injective coding
    whose codes along the canonical trajectory are LINEAR in the
    stage — logarithmic in the semantic value 2^j — so no growth
    separation can hold without the compositionality hypothesis.

    Construction: enumerate the trajectory first (stage j gets code
    2j), everything else by an explicit injective structural code on
    the odds. The definition uses classical choice only to decide
    trajectory membership; trajectory_index_le shows membership is
    decidable by bounded search (any hit has index at most twice the
    f₁ count), so the coding is computable in principle — the
    counterexample is fair against the "primitive recursive" reading
    of the conjecture. -/

/-- An explicit injective structural code, used off the trajectory.
    Leaves get 0, 1, 2; composite constructors get tagged Cantor
    pairs, offset to avoid the leaves. -/
def encodeT : Term → ℕ
  | .f₀ => 0
  | .f₁ => 1
  | .z => 2
  | .compose a b => 6 * Nat.pair (encodeT a) (encodeT b) + 3
  | .oplus a b => 6 * Nat.pair (encodeT a) (encodeT b) + 4
  | .obs a => 6 * encodeT a + 5

/-- The structural code is injective. -/
theorem encodeT_injective : Function.Injective encodeT := by
  intro t1 t2 h
  induction t1 generalizing t2 with
  | f₀ =>
    cases t2 <;> simp only [encodeT] at h <;> first | rfl | omega
  | f₁ =>
    cases t2 <;> simp only [encodeT] at h <;> first | rfl | omega
  | z =>
    cases t2 <;> simp only [encodeT] at h <;> first | rfl | omega
  | compose a b iha ihb =>
    cases t2 with
    | compose c d =>
      simp only [encodeT] at h
      have hp : Nat.pair (encodeT a) (encodeT b) =
          Nat.pair (encodeT c) (encodeT d) := by omega
      have hu := congrArg Nat.unpair hp
      rw [Nat.unpair_pair, Nat.unpair_pair] at hu
      rw [iha (congrArg Prod.fst hu), ihb (congrArg Prod.snd hu)]
    | _ => simp only [encodeT] at h; omega
  | oplus a b iha ihb =>
    cases t2 with
    | oplus c d =>
      simp only [encodeT] at h
      have hp : Nat.pair (encodeT a) (encodeT b) =
          Nat.pair (encodeT c) (encodeT d) := by omega
      have hu := congrArg Nat.unpair hp
      rw [Nat.unpair_pair, Nat.unpair_pair] at hu
      rw [iha (congrArg Prod.fst hu), ihb (congrArg Prod.snd hu)]
    | _ => simp only [encodeT] at h; omega
  | obs a iha =>
    cases t2 with
    | obs c =>
      simp only [encodeT] at h
      have : encodeT a = encodeT c := by omega
      rw [iha this]
    | _ => simp only [encodeT] at h; omega

/-- One Leibniz unfolding of an observation never loses f₁ leaves. -/
theorem f₁count_obsRewrite_obs_ge (w : Term) :
    f₁count w ≤ f₁count (obsRewrite (.obs w)) := by
  cases w <;> simp [obsRewrite, f₁count]

/-- Deep rewriting never loses f₁ leaves. -/
theorem f₁count_deepRewrite_ge (t : Term) :
    f₁count t ≤ f₁count (deepRewrite t) := by
  induction t with
  | obs u ih =>
    calc f₁count (.obs u) = f₁count u := rfl
      _ ≤ f₁count (deepRewrite u) := ih
      _ ≤ f₁count (obsRewrite (.obs (deepRewrite u))) :=
          f₁count_obsRewrite_obs_ge _
      _ = f₁count (deepRewrite (.obs u)) := rfl
  | compose a b iha ihb =>
    simp only [deepRewrite, f₁count]
    omega
  | oplus a b iha ihb =>
    simp only [deepRewrite, f₁count]
    omega
  | f₀ => exact le_refl _
  | f₁ => exact le_refl _
  | z => exact le_refl _

/-- The syntactic step never loses f₁ leaves. -/
theorem f₁count_synStep_ge (t : Term) :
    f₁count t ≤ f₁count (synStep t) := by
  have h := f₁count_deepRewrite_ge (.obs t)
  simpa [synStep, f₁count] using h

/-- The f₁ count is monotone along the trajectory. -/
theorem f₁count_trajectory_mono {i j : ℕ} (hij : i ≤ j) :
    f₁count (trajectory i) ≤ f₁count (trajectory j) := by
  induction j with
  | zero => simp [Nat.le_zero.mp hij]
  | succ j ih =>
    rcases Nat.lt_or_ge i (j + 1) with hlt | hge
    · exact le_trans (ih (by omega)) (f₁count_synStep_ge (trajectory j))
    · have : i = j + 1 := by omega
      simp [this]

/-- **BOUNDED SEARCH:** a trajectory hit's index is at most twice the
    f₁ count of the term. This makes trajectory membership decidable
    by bounded search, hence the compressed coding below computable
    in principle. -/
theorem trajectory_index_le (j : ℕ) :
    j ≤ 2 * f₁count (trajectory j) := by
  have h1 : 2 * (j / 2) ≤ j := by omega
  have h2 := f₁count_trajectory_mono h1
  rw [f₁count_trajectory] at h2
  have h3 : j / 2 + 1 ≤ 2 ^ (j / 2 + 1) :=
    Nat.le_of_lt (lt_two_pow_self' _)
  omega

open Classical in
/-- The compressed coding: trajectory stages on the evens (stage j
    gets at most 2j), everything else on the odds via encodeT. -/
noncomputable def compressedCode (t : Term) : ℕ :=
  if h : ∃ j, trajectory j = t then 2 * Nat.find h
  else 2 * encodeT t + 1

/-- The compressed coding is injective — no compositionality, but a
    perfectly faithful code. -/
theorem compressedCode_injective : Function.Injective compressedCode := by
  intro t1 t2 h
  unfold compressedCode at h
  split_ifs at h with h1 h2 h2
  · have hf : Nat.find h1 = Nat.find h2 := by omega
    have e1 := Nat.find_spec h1
    have e2 := Nat.find_spec h2
    rw [← e1, ← e2, hf]
  · omega
  · omega
  · have : encodeT t1 = encodeT t2 := by omega
    exact encodeT_injective this

/-- **COMPRESSION:** the compressed coding is linear along the
    trajectory — while the semantic value at stage j is 2^j. The
    quotation overhead of this injective coding is LOGARITHMIC in
    the meaning. -/
theorem compressedCode_trajectory_le (j : ℕ) :
    compressedCode (trajectory j) ≤ 2 * j := by
  have hex : ∃ i, trajectory i = trajectory j := ⟨j, rfl⟩
  rw [compressedCode, dif_pos hex]
  have := Nat.find_min' hex (rfl : trajectory j = trajectory j)
  omega

/-- **THE NON-COMPOSITIONAL CASE, REFUTED:** there is an injective
    coding of terms with linear codes along the canonical trajectory.
    Packaged form of the compression. -/
theorem compression_exists :
    ∃ ε : Term → ℕ, Function.Injective ε ∧
      ∀ j, ε (trajectory j) ≤ 2 * j :=
  ⟨compressedCode, compressedCode_injective, compressedCode_trajectory_le⟩

/-- **COMPOSITIONALITY IS NECESSARY:** the superpolynomial overhead
    theorem is FALSE when generalized from compositional codings to
    arbitrary injective codings — the compressed coding violates it
    already at coefficient 2, degree 1. The growth separation of
    Part 5 genuinely needs the compositionality hypothesis; the
    original conjecture's quantification over all primitive recursive
    injections cannot be repaired by any growth argument along a
    fixed trajectory. -/
theorem compositionality_necessary :
    ¬ ∀ ε : Term → ℕ, Function.Injective ε →
        ∀ a d : ℕ, ∃ m, a * (2 ^ (2 * m)) ^ d < ε (trajectory (2 * m)) := by
  intro hall
  obtain ⟨m, hm⟩ := hall compressedCode compressedCode_injective 2 1
  have hle := compressedCode_trajectory_le (2 * m)
  have h2m : 2 * m < 2 ^ (2 * m) := lt_two_pow_self' _
  rw [pow_one] at hm
  omega

/-! ## Part 8: Final Summary

    The growth question for the eval-quote square is now closed in
    both directions:

    | Coding class | Overhead along the trajectory | Theorem |
    |---|---|---|
    | Compositional | Superpolynomial in the meaning | quotation_overhead_superpolynomial |
    | Arbitrary injective | Linear in the stage is possible | compression_exists |

    Compositionality is exactly the boundary: it is what forces a
    code to pay for syntactic structure. An injective code free to
    ignore structure can name the trajectory as cheaply as counting
    its stages — quotation overhead is a property of HOW codes are
    built, not of coding per se. Together with Bisimulation.lean
    (extensionality is the qualitative boundary) this completes the
    answer to issue #55's open remainder. -/

end SpectralMonoid
