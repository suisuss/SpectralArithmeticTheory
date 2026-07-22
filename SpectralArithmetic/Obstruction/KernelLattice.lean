/-
  The Kernel Lattice: Degrees of Intensionality (Issue #68)
  =========================================================

  Trilemma.lean read the boundary theorem as a kernel statement: an
  observable supports a bisimulation iff its kernel contains eval's
  kernel. This file makes the kernel comparison an ORDER — degrees
  of intensionality — and locates the framework's observables on it.

  Convention: `KerLE o₁ o₂` reads "o₁ is at most as intensional as
  o₂", i.e. o₂ keeps every distinction o₁ keeps: Ker o₂ ⊆ Ker o₁.
  Larger = more intensional = smaller kernel = more distinctions
  retained. Under this convention the boundary theorem reads: the
  observables that support a bisimulation with A are exactly those
  lying at or below eval A on the order.

  Results (all sorry-free, no axioms):

  1. The order: KerLE is a preorder across heterogeneous codomains
     (KerLE.refl, KerLE.trans), with strict version KerLT.
  2. The poles: injective observables are maximally intensional —
     their kernel is equality, so everything lies below them
     (injective_kerLE, injective_iff_kerLE_id); constant observables
     are maximally extensional — total kernel, they lie below
     everything (constant_kerLE, constant_iff_kerLE_unit).
  3. Pairing: the paired observable's kernel is the intersection of
     kernels (ker_pair_iff) — the meet of kernels, hence the JOIN in
     the intensionality order: an upper bound of both components
     (kerLE_pair_left/right) and the least one (pair_kerLE).
  4. The operational threshold as a position on the order: o supports
     a bisimulation with A iff o ≤ eval A (supportsBisimF_iff_kerLE).
     The bisimulation-supporting class is therefore a down-set,
     closed under pairing (supportsBisimF_pair).
  5. Rewrite invariance as a kernel condition: o is rewrite-invariant
     iff its kernel contains every (t, deepRewrite t) pair
     (rewriteInvariantF_iff_ker); everything at or below eval is
     rewrite-invariant (rewriteInvariantF_of_kerLE).
  6. The strict hierarchy. Universal, pointwise: every injective
     observable sits STRICTLY above every rewrite-invariant
     observable (rewriteInvariantF_kerLT_injective), in particular
     strictly above eval (eval_kerLT_injective), and no injective
     observable is itself rewrite-invariant
     (injective_not_rewriteInvariantF). Model-relative, over the
     non-degenerate algebra natSuccAlgebra: a concrete three-point
     strict chain constant < eval < identity (kerLT_chain), and the
     middle strictness — a rewrite-invariant observable NOT below
     eval (exists_rewriteInvariantF_not_kerLE_eval), hence supporting
     no bisimulation (isConstF_no_bisimF). The middle witness is
     order-incomparable with eval (eval_not_kerLE_isConstF): the
     middle level of the hierarchy is a class, not a point on a
     chain through eval.
-/

import SpectralArithmetic.Obstruction.Trilemma

namespace UniversalObstruction

namespace TermF

variable {C : Type*} {S : Type*} {O O₁ O₂ O₃ : Type*}

/-! ## Part 1: The Intensionality Order

    The kernel of an observable is the compression it performs; the
    natural comparison is kernel inclusion, read contravariantly so
    that MORE intensional means MORE distinctions kept. Codomains
    are heterogeneous, so this is a preorder across a family of
    types, not a `Preorder` instance on one type; reflexivity and
    transitivity are explicit lemmas. -/

/-- `KerLE o₁ o₂`: o₁ is at most as intensional as o₂ — every
    distinction o₁ keeps, o₂ keeps too (equivalently, o₂'s kernel is
    contained in o₁'s). -/
def KerLE (o₁ : TermF C → O₁) (o₂ : TermF C → O₂) : Prop :=
  ∀ t₁ t₂, Ker o₂ t₁ t₂ → Ker o₁ t₁ t₂

/-- The intensionality order is reflexive. -/
theorem KerLE.refl (o : TermF C → O) : KerLE o o :=
  fun _ _ h => h

/-- The intensionality order is transitive. -/
theorem KerLE.trans {o₁ : TermF C → O₁} {o₂ : TermF C → O₂}
    {o₃ : TermF C → O₃} (h₁₂ : KerLE o₁ o₂) (h₂₃ : KerLE o₂ o₃) :
    KerLE o₁ o₃ :=
  fun t₁ t₂ h => h₁₂ t₁ t₂ (h₂₃ t₁ t₂ h)

/-- `KerLT o₁ o₂`: o₂ is strictly more intensional than o₁. -/
def KerLT (o₁ : TermF C → O₁) (o₂ : TermF C → O₂) : Prop :=
  KerLE o₁ o₂ ∧ ¬ KerLE o₂ o₁

/-! ## Part 2: The Two Poles

    Maximally intensional = lossless = kernel is equality: the
    injective observables (injective_ker_iff from Trilemma.lean).
    Maximally extensional = total loss = total kernel: the constant
    observables. Each pole is characterized by its position. -/

/-- The identity observable is maximally intensional: everything
    lies at or below it. -/
theorem kerLE_id (o : TermF C → O) :
    KerLE o (id : TermF C → TermF C) :=
  fun _ _ h => congrArg o h

/-- **THE INTENSIONAL POLE:** every observable is at most as
    intensional as an injective one — a lossless observable keeps
    all distinctions (its kernel is equality, injective_ker_iff). -/
theorem injective_kerLE {ε : TermF C → O} (hε : Function.Injective ε)
    (o : TermF C → O₁) : KerLE o ε :=
  fun t₁ t₂ h => congrArg o ((injective_ker_iff hε t₁ t₂).mp h)

/-- **POLE CHARACTERIZATION (top):** an observable is injective iff
    the identity — hence every observable — lies at or below it. -/
theorem injective_iff_kerLE_id {ε : TermF C → O} :
    Function.Injective ε ↔ KerLE (id : TermF C → TermF C) ε :=
  ⟨fun hε => injective_kerLE hε id, fun h t₁ t₂ ht => h t₁ t₂ ht⟩

/-- **THE EXTENSIONAL POLE:** a constant observable is at most as
    intensional as anything — it keeps no distinction at all. -/
theorem constant_kerLE {o : TermF C → O} (h : ∀ t₁ t₂, o t₁ = o t₂)
    (o' : TermF C → O₁) : KerLE o o' :=
  fun t₁ t₂ _ => h t₁ t₂

/-- **POLE CHARACTERIZATION (bottom):** an observable is constant
    iff it lies at or below the trivial (unit-valued) observable. -/
theorem constant_iff_kerLE_unit {o : TermF C → O} :
    (∀ t₁ t₂, o t₁ = o t₂) ↔ KerLE o (fun _ : TermF C => ()) :=
  ⟨fun h => constant_kerLE h _, fun h t₁ t₂ => h t₁ t₂ rfl⟩

/-! ## Part 3: Pairing Keeps the Union of Distinctions

    Two observables read jointly identify a pair of terms exactly
    when both do: the paired kernel is the intersection of kernels.
    Intersection of kernels = union of distinctions kept, so pairing
    is the least upper bound (join) in the intensionality order —
    equivalently, the meet in the kernel-inclusion order. -/

/-- **PAIRED KERNEL = INTERSECTION OF KERNELS:** the pairing
    observable identifies exactly what both components identify. -/
theorem ker_pair_iff (o₁ : TermF C → O₁) (o₂ : TermF C → O₂)
    (t₁ t₂ : TermF C) :
    Ker (fun t => (o₁ t, o₂ t)) t₁ t₂ ↔ Ker o₁ t₁ t₂ ∧ Ker o₂ t₁ t₂ :=
  ⟨fun h => ⟨congrArg Prod.fst h, congrArg Prod.snd h⟩,
   fun h => congrArg₂ Prod.mk h.1 h.2⟩

/-- The pairing is at least as intensional as its first component. -/
theorem kerLE_pair_left (o₁ : TermF C → O₁) (o₂ : TermF C → O₂) :
    KerLE o₁ (fun t => (o₁ t, o₂ t)) :=
  fun t₁ t₂ h => ((ker_pair_iff o₁ o₂ t₁ t₂).mp h).1

/-- The pairing is at least as intensional as its second component. -/
theorem kerLE_pair_right (o₁ : TermF C → O₁) (o₂ : TermF C → O₂) :
    KerLE o₂ (fun t => (o₁ t, o₂ t)) :=
  fun t₁ t₂ h => ((ker_pair_iff o₁ o₂ t₁ t₂).mp h).2

/-- **PAIRING IS THE LEAST UPPER BOUND:** anything at least as
    intensional as both components is at least as intensional as
    their pairing. -/
theorem pair_kerLE {o₁ : TermF C → O₁} {o₂ : TermF C → O₂}
    {o : TermF C → O} (h₁ : KerLE o₁ o) (h₂ : KerLE o₂ o) :
    KerLE (fun t => (o₁ t, o₂ t)) o :=
  fun t₁ t₂ h =>
    (ker_pair_iff o₁ o₂ t₁ t₂).mpr ⟨h₁ t₁ t₂ h, h₂ t₁ t₂ h⟩

/-! ## Part 4: The Operational Threshold as a Position on the Order

    The boundary theorem, restated on the order: bisimulation
    support is the property of lying at or below the semantic pole.
    The bisimulation-supporting observables form a down-set with
    eval as its top, and the down-set is closed under pairing. -/

/-- **THE THRESHOLD IS A POSITION:** an observable supports a
    bisimulation with A iff it is at most as intensional as eval A.
    Capacity to co-vary with execution begins exactly at the
    semantic pole. -/
theorem supportsBisimF_iff_kerLE (A : LeibnizAlgebra C S)
    (t₀ : TermF C) (o : TermF C → O) :
    SupportsBisimF A o ↔ KerLE o (eval A) :=
  supportsBisimF_iff_ker_le A t₀ o

/-- The bisimulation-supporting class is closed under pairing: joint
    observation of two semantics-compatible observables is
    semantics-compatible. -/
theorem supportsBisimF_pair (A : LeibnizAlgebra C S) (t₀ : TermF C)
    {o₁ : TermF C → O₁} {o₂ : TermF C → O₂}
    (h₁ : SupportsBisimF A o₁) (h₂ : SupportsBisimF A o₂) :
    SupportsBisimF A (fun t => (o₁ t, o₂ t)) :=
  (supportsBisimF_iff_kerLE A t₀ _).mpr
    (pair_kerLE ((supportsBisimF_iff_kerLE A t₀ o₁).mp h₁)
      ((supportsBisimF_iff_kerLE A t₀ o₂).mp h₂))

/-! ## Part 5: Rewrite Invariance as a Kernel Condition -/

/-- **REWRITE INVARIANCE IS A KERNEL CONDITION:** an observable is
    rewrite-invariant iff its kernel contains every pair of a term
    with its deep Leibniz rewrite. -/
theorem rewriteInvariantF_iff_ker (o : TermF C → O) :
    RewriteInvariantF o ↔ ∀ t, Ker o t (deepRewrite t) :=
  ⟨fun h t => (h t).symm, fun h t => (h t).symm⟩

/-- eval is rewrite-invariant: the deep rewrite pairs lie in its
    kernel (deepRewrite_eval). -/
theorem eval_rewriteInvariantF (A : LeibnizAlgebra C S) :
    RewriteInvariantF (eval A) :=
  deepRewrite_eval A

/-- Everything at or below eval on the order is rewrite-invariant:
    the extensional down-set sits inside the rewrite-invariant
    class. -/
theorem rewriteInvariantF_of_kerLE (A : LeibnizAlgebra C S)
    {o : TermF C → O} (h : KerLE o (eval A)) : RewriteInvariantF o :=
  fun t => h (deepRewrite t) t (deepRewrite_eval A t)

/-! ## Part 6: The Strict Hierarchy

    Universal, pointwise: rewrite invariance forces a non-trivial
    kernel (the deep rewrite moves obs(comp(t₀,t₀))), so every
    injective observable — kernel exactly equality — sits strictly
    above every rewrite-invariant one, and above eval in
    particular. Model-relative: over the non-degenerate algebra
    natSuccAlgebra, the order carries a genuine three-point strict
    chain, and the extensional-inside-rewrite-invariant inclusion is
    strict, with the witness incomparable to eval. -/

/-- The deep rewrite moves the universal witness term: its root
    changes from obs to add. -/
theorem deepRewrite_obs_comp_ne (t₀ : TermF C) :
    deepRewrite (.obs (.comp t₀ t₀)) ≠ .obs (.comp t₀ t₀) := by
  simp [deepRewrite, leibnizRewrite]

/-- No injective observable is rewrite-invariant: a lossless reading
    of syntax cannot absorb the eval-preserving rewrite. -/
theorem injective_not_rewriteInvariantF (t₀ : TermF C)
    {ε : TermF C → O} (hε : Function.Injective ε) :
    ¬ RewriteInvariantF ε :=
  fun h => deepRewrite_obs_comp_ne t₀ (hε (h (.obs (.comp t₀ t₀))))

/-- **STRICTNESS AT THE TOP, POINTWISE AND UNIVERSAL:** every
    injective observable is strictly more intensional than every
    rewrite-invariant observable, over every signature with a term.
    Rewrite invariance forces the kernel to contain a pair of
    distinct terms; equality contains none. -/
theorem rewriteInvariantF_kerLT_injective {o : TermF C → O₁}
    (h : RewriteInvariantF o) (t₀ : TermF C) {ε : TermF C → O}
    (hε : Function.Injective ε) : KerLT o ε := by
  refine ⟨injective_kerLE hε o, fun hle => ?_⟩
  have hk : Ker o (.obs (.comp t₀ t₀))
      (deepRewrite (.obs (.comp t₀ t₀))) :=
    (h (.obs (.comp t₀ t₀))).symm
  exact deepRewrite_obs_comp_ne t₀
    (hε (hle (.obs (.comp t₀ t₀)) _ hk)).symm

/-- **EQUALITY STRICTLY ABOVE THE SEMANTIC KERNEL, UNIVERSAL:**
    every injective observable is strictly more intensional than
    eval, in every Leibniz algebra with a term. -/
theorem eval_kerLT_injective (A : LeibnizAlgebra C S) (t₀ : TermF C)
    {ε : TermF C → O} (hε : Function.Injective ε) :
    KerLT (eval A) ε :=
  rewriteInvariantF_kerLT_injective (eval_rewriteInvariantF A) t₀ hε

/-- The root-constructor observable's kernel misses a deep-rewrite
    pair: rootTagF fails the kernel condition for rewrite
    invariance, over every signature with a term. -/
theorem rootTagF_ker_misses_rewrite (t₀ : TermF C) :
    ¬ ∀ t : TermF C, Ker rootTagF t (deepRewrite t) :=
  fun h => rootTagF_not_rewriteInvariantF t₀
    ((rewriteInvariantF_iff_ker rootTagF).mpr h)

/-- A non-degenerate Leibniz algebra on ℕ: zero and succ get
    distinct values, so eval is neither constant nor injective —
    strictly between the poles. The zero derivation satisfies the
    Leibniz law. -/
def natSuccAlgebra : LeibnizAlgebra PAConst ℕ where
  interpConst
    | .zero => 0
    | .succ => 1
  interpComp := (· * ·)
  interpAdd := (· + ·)
  interpObs _ := 0
  leibniz_law a b := by simp

/-- The constant observables sit strictly below eval in
    natSuccAlgebra: its semantics keeps at least one distinction. -/
theorem unit_kerLT_eval :
    KerLT (fun _ : TermF PAConst => ()) (eval natSuccAlgebra) := by
  refine ⟨constant_kerLE (fun _ _ => rfl) _, fun h => ?_⟩
  have hk := h (.const .zero) (.const .succ) rfl
  unfold Ker at hk
  exact absurd hk (by decide)

/-- **A THREE-POINT STRICT CHAIN:** constant < eval < identity, over
    the non-degenerate algebra. The semantic kernel sits strictly
    between the two poles of the order. -/
theorem kerLT_chain :
    KerLT (fun _ : TermF PAConst => ()) (eval natSuccAlgebra) ∧
      KerLT (eval natSuccAlgebra)
        (id : TermF PAConst → TermF PAConst) :=
  ⟨unit_kerLT_eval,
   eval_kerLT_injective natSuccAlgebra (.const .zero)
     fun _ _ h => h⟩

/-- Syntactic equality with a fixed constant, as a Boolean
    observable — the TermF counterpart of Bisimulation.lean's
    isF₀. -/
def isConstF [DecidableEq C] (c₀ : C) : TermF C → Bool :=
  fun t => decide (t = .const c₀)

/-- The Leibniz rewrite of an observation is never a bare constant:
    it is add-rooted or obs-rooted. -/
theorem leibnizRewrite_obs_ne_const (u : TermF C) (c : C) :
    leibnizRewrite (.obs u) ≠ .const c := by
  cases u <;> simp [leibnizRewrite]

/-- Constants are exactly the terms that deep-rewrite to a
    constant. -/
theorem deepRewrite_eq_const_iff (t : TermF C) (c : C) :
    deepRewrite t = .const c ↔ t = .const c := by
  cases t with
  | const c' => simp [deepRewrite]
  | comp a b => simp [deepRewrite]
  | add a b => simp [deepRewrite]
  | obs u =>
    simpa [deepRewrite] using
      leibnizRewrite_obs_ne_const (deepRewrite u) c

/-- isConstF is rewrite-invariant: normalization neither creates nor
    destroys bare constants. -/
theorem isConstF_rewriteInvariantF [DecidableEq C] (c₀ : C) :
    RewriteInvariantF (isConstF c₀) :=
  fun t => decide_eq_decide.mpr (deepRewrite_eq_const_iff t c₀)

/-- isConstF is not below eval in natSuccAlgebra: it separates
    const zero from comp(const zero, const zero), which the algebra
    identifies (0 = 0 * 0). -/
theorem isConstF_not_kerLE_eval :
    ¬ KerLE (isConstF PAConst.zero) (eval natSuccAlgebra) := by
  intro h
  have hk := h (.const .zero) (.comp (.const .zero) (.const .zero)) rfl
  unfold Ker isConstF at hk
  exact absurd hk (by decide)

/-- eval is not below isConstF either: eval separates const succ
    from add(const succ, const succ) (1 ≠ 2), which isConstF
    identifies (neither is const zero). The middle witness is
    order-INCOMPARABLE with eval — the middle level of the
    hierarchy is a class, not a point on a chain through eval. -/
theorem eval_not_kerLE_isConstF :
    ¬ KerLE (eval natSuccAlgebra) (isConstF PAConst.zero) := by
  intro h
  have hk := h (.const .succ) (.add (.const .succ) (.const .succ)) rfl
  unfold Ker at hk
  exact absurd hk (by decide)

/-- **MIDDLE STRICTNESS AT TermF LEVEL:** a rewrite-invariant
    observable of TermF PAConst that is not below eval — the
    extensional-inside-rewrite-invariant inclusion is strict for
    natSuccAlgebra. The witness is inherently model-relative (for
    the concrete spectral instance see Bisimulation.lean's isF₀);
    this is its universal-term-algebra counterpart. -/
theorem exists_rewriteInvariantF_not_kerLE_eval :
    ∃ o : TermF PAConst → Bool,
      RewriteInvariantF o ∧ ¬ KerLE o (eval natSuccAlgebra) :=
  ⟨isConstF PAConst.zero, isConstF_rewriteInvariantF PAConst.zero,
   isConstF_not_kerLE_eval⟩

/-- The middle witness supports no bisimulation: rewrite invariance
    is not sufficient for semantics-compatibility — the threshold
    sits exactly at eval, not at the rewrite-invariant class. -/
theorem isConstF_no_bisimF :
    ¬ SupportsBisimF natSuccAlgebra (isConstF PAConst.zero) :=
  fun h => isConstF_not_kerLE_eval
    ((supportsBisimF_iff_kerLE natSuccAlgebra (.const .zero) _).mp h)

/-! ## Part 7: Summary

    PROVED (sorry-free, no axioms):

    | Theorem | Content |
    |---------|---------|
    | KerLE.refl, KerLE.trans | The intensionality preorder |
    | injective_kerLE, injective_iff_kerLE_id | Injective = the top pole |
    | constant_kerLE, constant_iff_kerLE_unit | Constant = the bottom pole |
    | ker_pair_iff | Paired kernel = intersection of kernels |
    | kerLE_pair_left/right, pair_kerLE | Pairing = least upper bound |
    | supportsBisimF_iff_kerLE | Bisimulation support = position at or below eval |
    | supportsBisimF_pair | The down-set is closed under pairing |
    | rewriteInvariantF_iff_ker | Rewrite invariance as a kernel condition |
    | rewriteInvariantF_of_kerLE | Below eval implies rewrite-invariant |
    | rewriteInvariantF_kerLT_injective | Injective strictly above rewrite-invariant |
    | eval_kerLT_injective | Injective strictly above eval |
    | injective_not_rewriteInvariantF | No lossless observable is rewrite-invariant |
    | rootTagF_ker_misses_rewrite | rootTagF fails the kernel condition |
    | kerLT_chain | Constant < eval < identity (natSuccAlgebra) |
    | exists_rewriteInvariantF_not_kerLE_eval | Middle strictness at TermF level |
    | eval_not_kerLE_isConstF | The middle witness is incomparable with eval |
    | isConstF_no_bisimF | The threshold is eval, not rewrite invariance |

    UNIVERSAL vs MODEL-RELATIVE. Universal over every signature C
    with a term and every Leibniz algebra: the preorder, both pole
    characterizations, pairing as join, the threshold restatement,
    the kernel condition for rewrite invariance, and the pointwise
    strictness of injective observables over rewrite-invariant ones
    (hence over eval). Model-relative by nature: the three-point
    chain and the middle strictness, here witnessed over
    natSuccAlgebra on TermF PAConst (the concrete spectral witness
    is Bisimulation.lean's isF₀). No universal middle witness can
    exist: whether a rewrite-invariant observable escapes eval's
    down-set depends on which identifications the algebra makes
    beyond the forced Leibniz ones.

    THE PICTURE. Observables of syntax form a preordered spectrum
    from the constant pole (total compression) to the injective pole
    (lossless). eval sits strictly between them, and the boundary
    theorem places the capacity to track execution exactly at
    eval's down-set: strictly above it, and even incomparably beside
    it, bisimulation fails. Intensionality — stored distinctions —
    is precisely what disqualifies an observable from co-varying
    with the dynamics. -/

end TermF

end UniversalObstruction
