/-
  Interface Composition for Resolution Refutations (issue #45)
  ============================================================

  Modular SAT formulas admit short refutations when the inter-cluster
  interface is small. This file formalises the core composition lemma.

  Theorem (Interface Composition).
    Let F = F₁ ∪ F₂ where
      - F₁ uses only variables in (privateVars1 ∪ interface),
      - F₂ uses only variables in (privateVars2 ∪ interface),
      - privateVars1 ∩ privateVars2 = ∅.
    For each truth assignment α : interface → Bool, write F_i|α for
    the formula obtained by restricting F_i under α (drop satisfied
    clauses, drop falsified literals from the rest). If every F_i|α
    admits a resolution refutation of length ≤ L, then F admits a
    resolution refutation of length ≤ 2^|interface| · (2·L + 1).

  Why this matters for #45. For a chain of k clusters joined by a single
  bridge variable, |interface| = 1 between adjacent clusters, so the
  per-interface factor is constant (≤ 6). Recursing along the chain
  gives a resolution refutation of length poly(k) · 2^O(n) for Tseitin
  on chain-of-K_n — matching what solvers *should* find on modular
  instances and refuting the 2^Ω(k) lower-bound framing in #45.

  Phase A (this file): definitions + theorem statement. Proofs are `sorry`.
  Phase B: discharge the main theorem.
  Phase C: instantiate on chain-of-K_n modular Tseitin.
-/

import SpectralArithmetic.Rotation.Resolution
import SpectralArithmetic.Rotation.SATEncoding

set_option linter.style.longLine false

namespace RotationCalculus

open Term

/-! ## Interface decomposition -/

/-- A decomposition of a CNF formula into two sides sharing a variable
    interface. The private variable sets are disjoint; the interface is
    the shared boundary across which resolution must cross. -/
structure InterfaceDecomposition where
  formula1     : SATFormula
  formula2     : SATFormula
  interface    : List Nat
  privateVars1 : List Nat
  privateVars2 : List Nat
  deriving Repr

namespace InterfaceDecomposition

/-- Variables appearing in a single clause. -/
def clauseVars (c : SATClause) : List Nat := c.map (·.1)

/-- All variables of a formula (with duplicates). -/
def formulaVarsAll (F : SATFormula) : List Nat := F.flatMap clauseVars

/-- A clause is "on side 1" if every variable it mentions is either
    private to side 1 or on the interface. -/
def clauseOnSide1 (D : InterfaceDecomposition) (c : SATClause) : Prop :=
  ∀ v ∈ clauseVars c, v ∈ D.privateVars1 ∨ v ∈ D.interface

def clauseOnSide2 (D : InterfaceDecomposition) (c : SATClause) : Prop :=
  ∀ v ∈ clauseVars c, v ∈ D.privateVars2 ∨ v ∈ D.interface

/-- `D` is a valid decomposition of `F`. -/
def IsValid (D : InterfaceDecomposition) (F : SATFormula) : Prop :=
  (F = D.formula1 ++ D.formula2) ∧
  (∀ c ∈ D.formula1, D.clauseOnSide1 c) ∧
  (∀ c ∈ D.formula2, D.clauseOnSide2 c) ∧
  (∀ v, v ∈ D.privateVars1 → v ∉ D.privateVars2)

end InterfaceDecomposition

/-! ## Restriction of a formula under a partial assignment -/

/-- A partial assignment to variables. Each entry fixes one variable
    to a truth value. We do not assume completeness on any particular
    variable set. -/
abbrev PartialAssignment := List (Nat × Bool)

/-- Literal (v, p) is satisfied by assignment α iff α assigns v the value p. -/
def literalSat (α : PartialAssignment) (lit : Nat × Bool) : Bool :=
  α.any (fun (u, q) => u == lit.1 && q == lit.2)

/-- Literal (v, p) is falsified by α iff α assigns v the opposite value. -/
def literalFals (α : PartialAssignment) (lit : Nat × Bool) : Bool :=
  α.any (fun (u, q) => u == lit.1 && q != lit.2)

/-- Restrict a formula under α:
    - drop clauses containing a satisfied literal,
    - drop falsified literals from the rest. -/
def restrictFormula (F : SATFormula) (α : PartialAssignment) : SATFormula :=
  F.filterMap fun clause =>
    if clause.any (literalSat α) then none
    else some (clause.filter fun lit => !literalFals α lit)

/-! ## Enumerating interface assignments -/

/-- All 2^|B| truth assignments to the variables in B. -/
def allInterfaceAssignments : List Nat → List PartialAssignment
  | [] => [[]]
  | v :: rest =>
    let tail := allInterfaceAssignments rest
    tail.flatMap fun α => [(v, false) :: α, (v, true) :: α]

/-! ## Refutation-from-formula predicate

    A `Derivation` is a refutation of `F` if:
      - its conclusion is the empty clause,
      - each step's two premises are drawn either from `F` or from the
        results of earlier steps in the same derivation,
      - each step's `result` is the correct resolvent of its premises
        on the given pivot.
-/

/-- Premises of step `i` in `d` are *available* — either some F-clause
    (modulo weakening) or some previous step's result (modulo
    weakening) is a subset of the premise. The weakening on both sides
    matches the standard "resolution with weakening" presentation;
    for the lift construction it is essential, since the lifted
    derivation produces clauses that contain the original literals
    plus possibly additional ones from `falsifiedLiterals α` (and
    list ordering / dedup differs after the lift). -/
def stepPremisesValid (d : Derivation) (F : SATFormula) (i : Nat) : Prop :=
  match d.steps[i]? with
  | none => True
  | some step =>
    let prev := (d.steps.take i).map (·.result)
    ((∃ c₀ ∈ F, c₀ ⊆ step.clause1) ∨ (∃ p ∈ prev, p ⊆ step.clause1)) ∧
    ((∃ c₀ ∈ F, c₀ ⊆ step.clause2) ∨ (∃ p ∈ prev, p ⊆ step.clause2))

/-- Step `i`'s result equals `resolveOn` applied to its premises on its pivot. -/
def stepResultCorrect (d : Derivation) (i : Nat) : Prop :=
  match d.steps[i]? with
  | none => True
  | some step => step.result = resolveOn step.clause1 step.clause2 step.pivot

/-- `d.conclusion` is actually derived: either some F-clause is a
    subset of it (allowing weakening) or it equals some step's result.
    Required on top of "conclusion = []" so an empty Derivation cannot
    refute arbitrary `F`. The weakening matches `stepPremisesValid`. -/
def conclusionDerived (d : Derivation) (F : SATFormula) : Prop :=
  (∃ c₀ ∈ F, c₀ ⊆ d.conclusion) ∨ d.conclusion ∈ d.steps.map (·.result)

/-- `d` is a resolution refutation of `F`. -/
def RefutesFrom (d : Derivation) (F : SATFormula) : Prop :=
  d.conclusion = [] ∧
  conclusionDerived d F ∧
  (∀ i, i < d.steps.length →
    stepPremisesValid d F i ∧ stepResultCorrect d i)

/-! ## Lifting a restricted refutation back to the original formula

    Central construction for the composition theorem. Given a refutation
    of `F|α` and the falsified literals `L_α` of `α`, every clause
    appearing in the derivation is extended by appending `L_α`. Pivot
    variables are untouched because they are private to `F₁` or `F₂`
    and do not appear in `α`. The lifted derivation produces the clause
    `L_α` (instead of the empty clause).

    Two obligations for full correctness (deferred to named lemmas):
    - each lifted step remains a valid resolution step (pivot preserved,
      result unchanged modulo the appended literals),
    - each lifted original clause is present in `F` (weakening-closure
      requires the lifted clause to subsume some clause of `F`).
-/

/-- The list of falsified literals of an assignment α. Each `(v, b) ∈ α`
    contributes the literal `(v, !b)` (which α makes false). -/
def falsifiedLiterals (α : PartialAssignment) : SATClause :=
  α.map fun (v, b) => (v, !b)

/-- Lift a resolution step by appending extra literals to both premises.
    The `result` is **recomputed** via `resolveOn` so that
    `stepResultCorrect` holds definitionally for the lifted step.
    Pivot is unchanged. -/
def liftStep (extra : SATClause) (s : ResolutionStep) : ResolutionStep :=
  { clause1 := s.clause1 ++ extra
    clause2 := s.clause2 ++ extra
    pivot   := s.pivot
    result  := resolveOn (s.clause1 ++ extra) (s.clause2 ++ extra) s.pivot }

/-- Lift an entire derivation. The `conclusion` is set to `extra`
    (intended use: the original `d` is a refutation, `d.conclusion = []`,
    and `extra = falsifiedLiterals α` is what the lifted derivation
    proves from `F`). -/
def liftDerivation (extra : SATClause) (d : Derivation) : Derivation :=
  { steps      := d.steps.map (liftStep extra)
    conclusion := extra }

@[simp] lemma liftStep_pivot (extra : SATClause) (s : ResolutionStep) :
    (liftStep extra s).pivot = s.pivot := rfl

@[simp] lemma liftStep_result (extra : SATClause) (s : ResolutionStep) :
    (liftStep extra s).result =
      resolveOn (s.clause1 ++ extra) (s.clause2 ++ extra) s.pivot := rfl

@[simp] lemma liftStep_clause1 (extra : SATClause) (s : ResolutionStep) :
    (liftStep extra s).clause1 = s.clause1 ++ extra := rfl

@[simp] lemma liftStep_clause2 (extra : SATClause) (s : ResolutionStep) :
    (liftStep extra s).clause2 = s.clause2 ++ extra := rfl

@[simp] lemma liftDerivation_length (extra : SATClause) (d : Derivation) :
    (liftDerivation extra d).steps.length = d.steps.length := by
  simp [liftDerivation]

@[simp] lemma liftDerivation_conclusion (extra : SATClause) (d : Derivation) :
    (liftDerivation extra d).conclusion = extra := rfl

/-- Generalised derivation predicate: `d` derives the clause `c` from
    `F`. `RefutesFrom d F` is the special case `c = []`. -/
def DerivesFromTo (d : Derivation) (F : SATFormula) (c : SATClause) : Prop :=
  d.conclusion = c ∧
  conclusionDerived d F ∧
  (∀ i, i < d.steps.length →
    stepPremisesValid d F i ∧ stepResultCorrect d i)

/-- Bridge between `RefutesFrom` and `DerivesFromTo`: refutation is
    derivation of the empty clause. -/
lemma refutesFrom_iff_derivesFromTo_empty
    (d : Derivation) (F : SATFormula) :
    RefutesFrom d F ↔ DerivesFromTo d F [] := by
  simp [RefutesFrom, DerivesFromTo]

/-! ### Helper sub-lemmas for the lift

    Four small obligations whose proofs are list-algebra around
    `restrictFormula`, `resolveOn`, `eraseDups`, and `falsifiedLiterals`.
    Stated as named lemmas so each can be discharged independently of
    the main lift theorem. -/

/-- An α-falsified literal is in `falsifiedLiterals α`. The witness
    in α has variable matching the literal's and opposite polarity, so
    flipping (which is what `falsifiedLiterals` does) gives the literal. -/
private lemma falsified_imp_mem_falsifiedLiterals
    (lit : Nat × Bool) (α : PartialAssignment)
    (h : literalFals α lit) : lit ∈ falsifiedLiterals α := by
  unfold literalFals at h
  rw [List.any_eq_true] at h
  obtain ⟨⟨u, q⟩, huMem, huEq⟩ := h
  simp at huEq
  obtain ⟨huVar, huPol⟩ := huEq
  unfold falsifiedLiterals
  rw [List.mem_map]
  refine ⟨(u, q), huMem, ?_⟩
  obtain ⟨lv, lp⟩ := lit
  simp at huVar huPol ⊢
  refine ⟨huVar, ?_⟩
  cases q <;> cases lp <;> simp_all

/-- An F-clause with no α-satisfied literal is a subset of its
    α-restriction together with `falsifiedLiterals α`. Each literal of
    `C` is either kept by the restriction (lands in `C.filter (¬falsified)`)
    or falsified by α (lands in `falsifiedLiterals α`). -/
private lemma restrict_subset_extra
    (C : SATClause) (α : PartialAssignment)
    (_hNoSat : ¬ C.any (literalSat α)) :
    C ⊆ (C.filter (fun lit => !literalFals α lit)) ++ falsifiedLiterals α := by
  intro lit hLit
  by_cases hF : literalFals α lit
  · exact List.mem_append_right _ (falsified_imp_mem_falsifiedLiterals lit α hF)
  · apply List.mem_append_left
    rw [List.mem_filter]
    exact ⟨hLit, by simp [hF]⟩

/-- If `C ⊆ F` restricts to the empty clause under α (i.e., every
    literal of C is α-falsified and none is α-satisfied), then C is a
    subset of `falsifiedLiterals α`. -/
private lemma empty_in_restrict_witness
    (F : SATFormula) (α : PartialAssignment)
    (hMem : [] ∈ restrictFormula F α) :
    ∃ C ∈ F, C ⊆ falsifiedLiterals α := by
  unfold restrictFormula at hMem
  rw [List.mem_filterMap] at hMem
  obtain ⟨c, hcF, hcSome⟩ := hMem
  -- Avoid simp's aggressive expansion: case on the if-condition manually.
  by_cases hAny : c.any (literalSat α) = true
  · rw [if_pos hAny] at hcSome
    exact absurd hcSome (by simp)
  · rw [if_neg hAny] at hcSome
    rw [Option.some_inj] at hcSome
    -- hcSome : c.filter (fun lit => !literalFals α lit) = []
    refine ⟨c, hcF, ?_⟩
    intro lit hLit
    have hLitFals : literalFals α lit := by
      by_contra hNot
      have hFilt : lit ∈ c.filter (fun l => !literalFals α l) :=
        List.mem_filter.mpr ⟨hLit, by simp [hNot]⟩
      rw [hcSome] at hFilt
      exact List.not_mem_nil hFilt
    exact falsified_imp_mem_falsifiedLiterals lit α hLitFals

/-- Resolution commutes with weakening (set-subset form): when the
    pivot is not in `extra`'s variables, lifting the inputs by `extra`
    yields a resolvent with the same literal set as the unlifted
    resolvent appended with `extra`. List equality fails (order +
    dedup), but List.Subset both ways holds. -/
private lemma resolveOn_lift_subset
    (c1 c2 extra : SATClause) (v : Nat)
    (_hPiv : v ∉ extra.map (·.1)) :
    resolveOn (c1 ++ extra) (c2 ++ extra) v ⊆
      resolveOn c1 c2 v ++ extra ∧
    resolveOn c1 c2 v ++ extra ⊆
      resolveOn (c1 ++ extra) (c2 ++ extra) v := by
  sorry

/-- A clause with no occurrence of variable `v` is fixed by
    `filter (fun (v', _) => v' != v)`. Used to keep `extra` whole
    inside the lifted resolveOn (since the pivot is private). -/
private lemma filter_self_of_var_notMem
    (extra : SATClause) (v : Nat) (hPiv : v ∉ extra.map (·.1)) :
    extra.filter (fun (v', _) => v' != v) = extra := by
  apply List.filter_eq_self.mpr
  intro lit hLit
  simp only [bne_iff_ne, ne_eq]
  intro hEq
  apply hPiv
  rw [List.mem_map]
  exact ⟨lit, hLit, hEq⟩

/-- `(extra ++ extra).eraseDups = extra` when `extra.Nodup`.
    The proof reduces to: eraseDups keeps first occurrence; the first
    occurrence of every `extra`-element in `extra ++ extra` is in the
    left half; for Nodup `extra`, eraseDups is the identity.
    Stated as a named obligation; the body is List algebra around
    `List.eraseDups` which depends on Mathlib lemmas not yet wired
    up here. -/
private lemma eraseDups_double_of_nodup
    (extra : SATClause) (_hNodup : extra.Nodup) :
    (extra ++ extra).eraseDups = extra := by
  sorry

/-- For a step that already produces the empty clause, lifting yields
    a step that produces exactly `extra`. Requires `extra.Nodup` so
    that `(extra ++ extra).eraseDups = extra`. -/
private lemma resolveOn_lift_eq_extra_of_empty
    (c1 c2 extra : SATClause) (v : Nat)
    (hPiv : v ∉ extra.map (·.1))
    (hNodup : extra.Nodup)
    (hEmpty : resolveOn c1 c2 v = []) :
    resolveOn (c1 ++ extra) (c2 ++ extra) v = extra := by
  unfold resolveOn at hEmpty ⊢
  -- Decompose hEmpty: `(c1.filter (≠v) ++ c2.filter (≠v)).eraseDups = []`,
  -- and eraseDups gives [] iff input is [].
  have hMergedNil :
      c1.filter (fun (v', _) => v' != v) ++
        c2.filter (fun (v', _) => v' != v) = [] := by
    -- If the merged list were nonempty, `eraseDups` would keep some
    -- element, contradicting hEmpty. Deferred as a 1-line sub-obligation
    -- (Mathlib name lookup for eraseDups-preserves-membership).
    sorry
  obtain ⟨hC1Empty, hC2Empty⟩ := List.append_eq_nil_iff.mp hMergedNil
  -- Now lifted resolveOn: (c1 ++ extra).filter (≠v) = c1.filter ++ extra
  --                     = [] ++ extra = extra.
  rw [List.filter_append, List.filter_append, hC1Empty, hC2Empty]
  rw [filter_self_of_var_notMem extra v hPiv]
  simp only [List.nil_append]
  exact eraseDups_double_of_nodup extra hNodup

/-! ### The lifting lemma -/

/-- **Lifting lemma (central Phase B obligation).**

    If `d` refutes `F|α` and each pivot of `d` is disjoint from `α`'s
    domain, and `falsifiedLiterals α` has no duplicate literals, then
    `F` admits a derivation of `falsifiedLiterals α` of the same length.

    **Proof.** The witness is `liftDerivation (falsifiedLiterals α) d`,
    which appends `extra := falsifiedLiterals α` to every step's
    premises and recomputes each step's result via `resolveOn`. The
    `stepResultCorrect` obligation is satisfied definitionally by the
    new `liftStep`. The `stepPremisesValid` obligation reduces to two
    cases per premise:

    - **From F|α**: an F-clause `C₀` restricted to a sub-clause `c₀ ⊆ premise`.
      Lemma `restrict_subset_extra` gives `C₀ ⊆ premise ++ extra`,
      so the lifted premise is a weakening of `C₀ ∈ F`.
    - **From prior result**: a previous step `j` produced `p ⊆ premise`.
      Lemma `resolveOn_lift_subset` gives that the lifted j-th result
      has the same literal set as `p ++ extra`, hence is ⊆ `premise ++ extra`.

    The `conclusionDerived` obligation: either `[] ∈ restrictFormula F α`
    (handled via `empty_in_restrict_witness` — some F-clause is ⊆ extra)
    or some original step produced `[]` (handled via
    `resolveOn_lift_eq_extra_of_empty` — its lifted result equals
    `extra`). -/
lemma lift_refutation_to_derivation
    (F : SATFormula) (α : PartialAssignment) (d : Derivation)
    (_hRef : RefutesFrom d (restrictFormula F α))
    (_hαNodup : (falsifiedLiterals α).Nodup)
    (_hPivotsPrivate :
      ∀ i (h : i < d.steps.length),
        (d.steps[i]'h).pivot ∉ α.map (·.1)) :
    ∃ d' : Derivation,
      DerivesFromTo d' F (falsifiedLiterals α) ∧
      d'.steps.length ≤ d.steps.length := by
  -- Witness: the lifted derivation. Its conclusion is `extra` by
  -- definition; length equals d's by `liftDerivation_length`.
  -- The full validity argument is the body the helper lemmas above
  -- close together; deferred until the helpers are discharged.
  sorry

/-! ## Restriction-by-empty is the identity -/

@[simp] lemma literalSat_empty (lit : Nat × Bool) :
    literalSat [] lit = false := rfl

@[simp] lemma literalFals_empty (lit : Nat × Bool) :
    literalFals [] lit = false := rfl

@[simp] lemma restrictFormula_empty (F : SATFormula) :
    restrictFormula F [] = F := by
  unfold restrictFormula
  induction F with
  | nil => rfl
  | cons c rest ih =>
    simp only [List.filterMap_cons]
    have hAny : c.any (literalSat []) = false := by
      simp [List.any_eq_false]
    have hFilt : c.filter (fun lit => !literalFals [] lit) = c := by
      apply List.filter_eq_self.mpr
      intro lit _
      simp
    rw [if_neg (by simp [hAny])]
    rw [hFilt]
    simp
    -- ih closes the recursive call on `rest`

/-! ## Monotonicity of `RefutesFrom`

    If `d` refutes `F` and `F ⊆ F'` (pointwise list containment), then
    `d` also refutes `F'`. Used to lift a refutation of `F₁` or `F₂`
    to a refutation of `F = F₁ ++ F₂`. -/

/-- Per-step monotonicity: if step `i`'s premises come from `F` (modulo
    weakening) or prior results, and `F ⊆ F'`, then they come from `F'`
    (modulo weakening) or prior results. -/
private lemma stepPremisesValid_mono
    {d : Derivation} {F F' : SATFormula}
    (hSub : ∀ c ∈ F, c ∈ F') (i : Nat)
    (h : stepPremisesValid d F i) : stepPremisesValid d F' i := by
  simp only [stepPremisesValid] at h ⊢
  match hs : d.steps[i]? with
  | none => trivial
  | some step =>
    rw [hs] at h
    obtain ⟨h1, h2⟩ := h
    refine ⟨?_, ?_⟩
    · rcases h1 with ⟨c₀, hMem, hSubC⟩ | hPrev
      · exact Or.inl ⟨c₀, hSub _ hMem, hSubC⟩
      · exact Or.inr hPrev
    · rcases h2 with ⟨c₀, hMem, hSubC⟩ | hPrev
      · exact Or.inl ⟨c₀, hSub _ hMem, hSubC⟩
      · exact Or.inr hPrev

/-- Extension of `RefutesFrom` under formula subsetting. -/
lemma RefutesFrom_mono
    (d : Derivation) (F F' : SATFormula)
    (hSub : ∀ c ∈ F, c ∈ F')
    (hRef : RefutesFrom d F) : RefutesFrom d F' := by
  obtain ⟨hConcl, hDerived, hSteps⟩ := hRef
  refine ⟨hConcl, ?_, ?_⟩
  · rcases hDerived with ⟨c₀, hMem, hSubC⟩ | hPrev
    · exact Or.inl ⟨c₀, hSub _ hMem, hSubC⟩
    · exact Or.inr hPrev
  · intro i hi
    obtain ⟨hPrem, hResult⟩ := hSteps i hi
    exact ⟨stepPremisesValid_mono hSub i hPrem, hResult⟩

/-! ## Combining two derivations via a final resolution step -/

/-- Concatenate `d1 ++ d2` and append one resolution step whose premises
    are the two conclusions. The combined derivation concludes with the
    resolvent. Length = d1.length + d2.length + 1. -/
def concatResolve (d1 d2 : Derivation) (pivot : Nat) : Derivation :=
  let finalStep : ResolutionStep :=
    { clause1 := d1.conclusion
      clause2 := d2.conclusion
      pivot   := pivot
      result  := resolveOn d1.conclusion d2.conclusion pivot }
  { steps      := d1.steps ++ d2.steps ++ [finalStep]
    conclusion := finalStep.result }

@[simp] lemma concatResolve_length
    (d1 d2 : Derivation) (pivot : Nat) :
    (concatResolve d1 d2 pivot).steps.length =
      d1.steps.length + d2.steps.length + 1 := by
  simp [concatResolve, Nat.add_assoc]

/-! ## The composition theorem (statement only — Phase A) -/

/-- Shorthand: the length of a derivation. -/
def Derivation.length (d : Derivation) : Nat := d.steps.length

/-- **Base case: empty interface.**

    When `D.interface = []` the only assignment is `[]`, both `F_i|[] = F_i`,
    so the hypothesis directly gives a refutation of either `F₁` or `F₂`.
    Since `F = F₁ ++ F₂`, monotonicity (`RefutesFrom_mono`) lifts the
    side-refutation to a refutation of `F`. The length bound `L ≤ 2L + 1`
    matches `2^0 * (2L + 1)`.

    This is closed (no `sorry`), provides the base case for the general
    induction, and demonstrates the lift-free part of the proof. -/
lemma interfaceComposition_emptyInterface
    (F : SATFormula)
    (D : InterfaceDecomposition)
    (hValid : D.IsValid F)
    (hEmpty : D.interface = [])
    (L : Nat)
    (hSides :
      ∀ α ∈ allInterfaceAssignments D.interface,
        (∃ d1 : Derivation,
           RefutesFrom d1 (restrictFormula D.formula1 α) ∧
           d1.length ≤ L) ∧
        (∃ d2 : Derivation,
           RefutesFrom d2 (restrictFormula D.formula2 α) ∧
           d2.length ≤ L))
    : ∃ d : Derivation,
        RefutesFrom d F ∧
        d.length ≤ 2 * L + 1 := by
  -- Empty interface ⇒ allInterfaceAssignments is just `[[]]`.
  have hAssign : allInterfaceAssignments D.interface = [[]] := by
    rw [hEmpty]; rfl
  have hMem : ([] : PartialAssignment) ∈ allInterfaceAssignments D.interface := by
    rw [hAssign]; simp
  -- Pick the F₁ refutation under the trivial assignment.
  obtain ⟨⟨d1, hd1Ref, hd1Len⟩, _⟩ := hSides [] hMem
  -- restrictFormula F₁ [] = F₁.
  rw [restrictFormula_empty] at hd1Ref
  -- Lift d1 from F₁ to F = F₁ ++ F₂ via monotonicity.
  have hSub : ∀ c ∈ D.formula1, c ∈ F := by
    intro c hc
    obtain ⟨hF, _, _, _⟩ := hValid
    rw [hF]; exact List.mem_append_left _ hc
  refine ⟨d1, RefutesFrom_mono d1 D.formula1 F hSub hd1Ref, ?_⟩
  -- Length bound: d1.length ≤ L ≤ 2L + 1.
  unfold Derivation.length at hd1Len ⊢
  omega

/-- **Theorem (Interface Composition) — Phase A statement.**

    Let D be a valid interface decomposition of F. Suppose for every
    truth assignment α over D.interface there exist resolution
    refutations of F₁|α and F₂|α, each of length at most L. Then there
    exists a resolution refutation of F of length at most
    `2^|interface| · (2·L + 1)`.

    The `+ 1` per assignment covers the case-split/merge step that
    combines the two refutations under that interface branch. -/
theorem interfaceComposition_length
    (F : SATFormula)
    (D : InterfaceDecomposition)
    (hValid : D.IsValid F)
    (L : Nat)
    (hSides :
      ∀ α ∈ allInterfaceAssignments D.interface,
        (∃ d1 : Derivation,
           RefutesFrom d1 (restrictFormula D.formula1 α) ∧
           d1.length ≤ L) ∧
        (∃ d2 : Derivation,
           RefutesFrom d2 (restrictFormula D.formula2 α) ∧
           d2.length ≤ L))
    : ∃ d : Derivation,
        RefutesFrom d F ∧
        d.length ≤ 2 ^ D.interface.length * (2 * L + 1) := by
  -- Case-split on |interface|: base = 0, inductive step ≥ 1.
  match hLen : D.interface.length with
  | 0 =>
    -- Empty interface: dispatch to the closed base case.
    have hEmpty : D.interface = [] := by
      match h : D.interface with
      | [] => rfl
      | _ :: _ => rw [h] at hLen; simp at hLen
    obtain ⟨d, hRef, hLenBound⟩ :=
      interfaceComposition_emptyInterface F D hValid hEmpty L hSides
    refine ⟨d, hRef, ?_⟩
    -- 2^0 * (2L + 1) = 2L + 1, so the bound matches.
    simp only [pow_zero, one_mul]
    exact hLenBound
  | _ + 1 =>
    -- Inductive step: peel off one variable from the interface, apply
    -- the single-bridge composition (or its k-fold iterate) recursively.
    -- Open obligation: depends on `interfaceComposition_singleBridge`
    -- (and hence on `lift_refutation_to_derivation`).
    sorry

/-! ## Corollary for single-variable interfaces

    For |interface| = 1 (the chain-of-clusters single-bridge case),
    the bound simplifies to `2 · (2L + 1) = 4L + 2`, i.e. linear in L.
    This is the shape that makes chain-composition give poly(k).

    Stated separately so downstream code does not have to re-expose
    the 2^_ bookkeeping in the simple case. -/
theorem interfaceComposition_singleBridge
    (F : SATFormula)
    (D : InterfaceDecomposition)
    (hValid : D.IsValid F)
    (hSingleBridge : D.interface.length = 1)
    (L : Nat)
    (hSides :
      ∀ α ∈ allInterfaceAssignments D.interface,
        (∃ d1 : Derivation,
           RefutesFrom d1 (restrictFormula D.formula1 α) ∧
           d1.length ≤ L) ∧
        (∃ d2 : Derivation,
           RefutesFrom d2 (restrictFormula D.formula2 α) ∧
           d2.length ≤ L))
    : ∃ d : Derivation,
        RefutesFrom d F ∧
        d.length ≤ 4 * L + 2 := by
  -- Extract the single bridge variable b.
  have ⟨b, hb⟩ : ∃ b, D.interface = [b] := by
    match h : D.interface with
    | [] => simp [h] at hSingleBridge
    | [b] => exact ⟨b, rfl⟩
    | _ :: _ :: _ => simp [h] at hSingleBridge
  -- The two assignments over interface=[b].
  let αF : PartialAssignment := [(b, false)]
  let αT : PartialAssignment := [(b, true)]
  have hαF_mem : αF ∈ allInterfaceAssignments D.interface := by
    rw [hb]; simp [allInterfaceAssignments, αF]
  have hαT_mem : αT ∈ allInterfaceAssignments D.interface := by
    rw [hb]; simp [allInterfaceAssignments, αT]
  -- From hSides we get refutations for each side under each α.
  have ⟨d1F_ex, _⟩ := hSides αF hαF_mem
  have ⟨_, d2T_ex⟩ := hSides αT hαT_mem
  -- Open the existentials.
  obtain ⟨d1F, hd1F_ref, hd1F_len⟩ := d1F_ex
  obtain ⟨d2T, hd2T_ref, hd2T_len⟩ := d2T_ex
  -- Lift them to derivations of {b} (from αF, literals falsified is (b,T))
  -- and {¬b} (from αT, literals falsified is (b,F)) on their respective
  -- private sides.
  -- NOTE: lift_refutation_to_derivation needs a pivot-disjointness hyp;
  -- in valid decompositions, F_i's clauses only mention privateVars_i ∪
  -- interface, and resolution pivots within F_i must be variables that
  -- appear in its clauses with opposite polarity — a pivot equal to
  -- interface var `b` is only possible if `b` is mentioned in clauses
  -- of F_i. Since α fixes b, any such clause is either satisfied or has
  -- its (b, _) literal dropped under restriction, so after restriction
  -- `b` never appears as a pivot. This is the hPivotsPrivate condition,
  -- which follows from hd1F_ref / hd2T_ref + hValid but is also left
  -- as an obligation (pushed to the lift lemma) in this Phase B step.
  -- For now we just thread the hypothesis through.
  sorry

/-! ## Smoke test: definitions compute on small inputs -/

/-- Trivially UNSAT formula {x₀} ∧ {¬x₀} with trivial interface. -/
private def smokeFormula : SATFormula := [[(0, true)], [(0, false)]]

private def smokeDecomp : InterfaceDecomposition :=
  { formula1     := [[(0, true)]]
    formula2     := [[(0, false)]]
    interface    := [0]
    privateVars1 := []
    privateVars2 := [] }

#eval (allInterfaceAssignments smokeDecomp.interface).length
      -- expect 2

#eval (restrictFormula smokeDecomp.formula1 [(0, true)]).length
      -- expect 0 (clause satisfied)

#eval (restrictFormula smokeDecomp.formula1 [(0, false)]).length
      -- expect 1 (clause becomes empty — an immediate refutation of length 0)

end RotationCalculus
