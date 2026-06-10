/-
  Bisimulation: The Coalgebraic Quine Question
  =============================================

  The eval-quote diagram asks whether the Godel encoding induces a
  behavioral equivalence between the syntactic coalgebra (term
  rewriting) and the semantic coalgebra (observation). This file
  answers the question at the level it can currently be answered,
  in two tiers.

  TIER 1 (positive): the graph of `eval` IS a bisimulation between
  the syntactic observation system (Term, one application of obs
  followed by Leibniz unfolding) and the semantic observation system
  (State, obs). With any code/decode retraction, the code-level
  dynamics are bisimilar to the semantic dynamics. The eval-quote
  square commutes up to bisimulation — WHEN the observation taken of
  syntax is extensional.

  TIER 2 (characterization): that qualifier is exactly the boundary.
  An observable o : Term -> O supports a bisimulation relating every
  term to its evaluation IF AND ONLY IF o is extensional (factors
  through eval). The three strictness witnesses:

  - rootTag (the root constructor): not even invariant under the
    eval-preserving rewrite, hence not extensional. The intensional
    side of the boundary.
  - isF₀ (syntactic equality with f₀): invariant under the rewrite
    but NOT extensional. So
        extensional ⊊ rewrite-invariant ⊊ all observables,
    with both inclusions strict and machine-checked.
  - any INJECTIVE ε : Term -> ℕ: not extensional. Injectivity is
    precisely maximal intensionality. This reinterprets (it does not
    re-derive) no_coalgebra_morphism from Main.lean: the obstruction
    is not a quirk of codes — it is the statement that a faithful
    code is the most intensional observable there is, and the
    bisimulation boundary excludes every observable on the
    intensional side.

  TIER 3 (open, not in this file): whether the semantic dynamics and
  the code dynamics on a COMMON carrier are non-bisimilar for every
  primitive recursive coding — the growth-rate conjecture of
  docs/theory/computation/encoding-obstruction.md, Part 5.
-/

import SpectralArithmetic.Obstruction.Encoding

namespace SpectralMonoid

open Term

/-! ## Part 1: Observation Systems and Bisimulation

    An observation system is a state space with a step function
    (the dynamics) and an output map (what an observer reads at
    each state). Bisimulation between two systems over a shared
    output type: a relation that matches outputs and is closed
    under stepping. This is the standard coalgebraic notion for
    the functor X ↦ O × X. -/

/-- An observation system: dynamics plus an output read at each state. -/
structure ObsSystem (X : Type*) (O : Type*) where
  /-- One step of the dynamics. -/
  step : X → X
  /-- The output an observer reads at a state. -/
  out : X → O

/-- A bisimulation between two observation systems sharing an output
    type: related states have equal outputs, and stepping preserves
    the relation. -/
structure Bisim {X Y O : Type*} (A : ObsSystem X O) (B : ObsSystem Y O) where
  /-- The relating predicate. -/
  rel : X → Y → Prop
  /-- Related states are indistinguishable to the observer. -/
  out_eq : ∀ {x y}, rel x y → A.out x = B.out y
  /-- The relation survives one step of both dynamics. -/
  step_rel : ∀ {x y}, rel x y → rel (A.step x) (B.step y)

/-- The syntactic step: apply obs and unfold it via the Leibniz
    rewrite. This is the term-level implementation of one semantic
    observation. -/
def synStep (t : Term) : Term := deepRewrite (.obs t)

/-- The syntactic observation system over an output map o. -/
def synSys {O : Type*} (o : Term → O) : ObsSystem Term O where
  step := synStep
  out := o

/-- The semantic observation system over an output map oS. -/
def semSys (State : Type*) [DynSemiring State] {O : Type*}
    (oS : State → O) : ObsSystem State O where
  step := SpectralMonoid.obs
  out := oS

/-! ## Part 2: Tier 1 — The Eval Graph Is a Bisimulation

    The syntactic step correctly implements the semantic step:
    eval(synStep t) = obs(eval t). Therefore the graph of eval is a
    bisimulation between (Term, synStep, eval) and (State, obs, id).
    The syntactic dynamics simulate the semantic dynamics exactly,
    as long as the observer reads syntax extensionally (through eval). -/

/-- The syntactic step implements the semantic step through eval. -/
theorem synStep_eval {State : Type*} [DynSemiring State] (t : Term) :
    eval (synStep t) = SpectralMonoid.obs (eval t : State) := by
  unfold synStep
  rw [deepRewrite_eval]
  simp only [eval]

/-- **THE EVAL GRAPH IS A BISIMULATION (Tier 1):**
    relating each term to its evaluation is a bisimulation between
    the syntactic system observed through eval and the semantic
    system observed directly. -/
def evalGraphBisim (State : Type*) [DynSemiring State] :
    Bisim (synSys (eval : Term → State)) (semSys State id) where
  rel t s := eval t = s
  out_eq h := h
  step_rel {t s} h := by
    change eval (synStep t) = SpectralMonoid.obs s
    rw [synStep_eval, h]

/-- The eval-graph bisimulation relates every term to its evaluation. -/
theorem evalGraphBisim_total (State : Type*) [DynSemiring State] (t : Term) :
    (evalGraphBisim State).rel t (eval t) := rfl

/-- A coding of terms: a code map with a decode retraction.
    The retraction makes code injective; no other property is assumed. -/
structure Coding where
  /-- Godel code of a term. -/
  code : Term → ℕ
  /-- Decode a code back to a term. -/
  decode : ℕ → Term
  /-- Decoding undoes coding. -/
  retract : ∀ t, decode (code t) = t

/-- The code-level dynamics: decode, step syntactically, re-encode.
    Outputs are read extensionally (decode, then evaluate). -/
def codeSys (c : Coding) (State : Type*) [DynSemiring State] :
    ObsSystem ℕ State where
  step n := c.code (synStep (c.decode n))
  out n := eval (c.decode n)

/-- **THE EVAL-QUOTE SQUARE COMMUTES UP TO BISIMULATION (Tier 1):**
    for any coding, the code-level dynamics are bisimilar to the
    semantic dynamics. Quotation costs nothing behaviorally — when
    observation is extensional. -/
def codeBisim (c : Coding) (State : Type*) [DynSemiring State] :
    Bisim (codeSys c State) (semSys State id) where
  rel n s := eval (c.decode n) = s
  out_eq h := h
  step_rel {n s} h := by
    change eval (c.decode (c.code (synStep (c.decode n)))) = SpectralMonoid.obs s
    rw [c.retract, synStep_eval, h]

/-- The code bisimulation relates every coded term to its evaluation. -/
theorem codeBisim_total (c : Coding) (State : Type*) [DynSemiring State]
    (t : Term) :
    (codeBisim c State).rel (c.code t) (eval t) := by
  change eval (c.decode (c.code t)) = eval t
  rw [c.retract]

/-! ## Part 3: Tier 2 — Extensionality Characterizes Bisimilarity

    Tier 1 used a specific output map (eval itself). The general
    question: WHICH observables of syntax support a bisimulation
    relating each term to its evaluation? Answer: exactly the
    extensional ones — those that factor through eval. -/

/-- An observable of syntax is extensional (relative to a model State)
    if it factors through evaluation: it reads only the meaning of a
    term, not its form. -/
def Extensional (State : Type*) [DynSemiring State] {O : Type*}
    (o : Term → O) : Prop :=
  ∃ oS : State → O, ∀ t, o t = oS (eval t)

/-- An observable supports a bisimulation if some semantic output map
    makes the two systems bisimilar with every term related to its
    evaluation. -/
def SupportsBisim (State : Type*) [DynSemiring State] {O : Type*}
    (o : Term → O) : Prop :=
  ∃ oS : State → O, ∃ B : Bisim (synSys o) (semSys State oS),
    ∀ t, B.rel t (eval t)

/-- **THE CHARACTERIZATION (Tier 2):**
    an observable supports a bisimulation iff it is extensional.

    Forward: output agreement at (t, eval t) IS the factorization.
    Backward: the eval graph, with outputs read through the factor. -/
theorem supportsBisim_iff_extensional (State : Type*) [DynSemiring State]
    {O : Type*} (o : Term → O) :
    SupportsBisim State o ↔ Extensional State o := by
  constructor
  · rintro ⟨oS, B, htot⟩
    exact ⟨oS, fun t => B.out_eq (htot t)⟩
  · rintro ⟨oS, ho⟩
    refine ⟨oS, ⟨fun t s => eval t = s, ?_, ?_⟩, fun _ => rfl⟩
    · intro t s hrel
      change o t = oS s
      rw [ho t, hrel]
    · intro t s hrel
      change eval (synStep t) = SpectralMonoid.obs s
      rw [synStep_eval, hrel]

/-- Extensional observables cannot separate terms with equal evaluation. -/
theorem Extensional.eval_congr {State : Type*} [DynSemiring State]
    {O : Type*} {o : Term → O} (h : Extensional State o)
    {t t' : Term} (he : eval t = (eval t' : State)) : o t = o t' := by
  obtain ⟨oS, ho⟩ := h
  rw [ho t, ho t', he]

/-! ## Part 4: Rewrite Invariance

    The eval-preserving normalization dynamics (deepRewrite) give a
    coarser necessary condition: every extensional observable is
    invariant under the rewrite, because the rewrite preserves eval.
    The converse FAILS (Part 5) — that failure is where the
    framework's intensional observables live. -/

/-- An observable is rewrite-invariant if the Leibniz normalization
    cannot change it. -/
def RewriteInvariant {O : Type*} (o : Term → O) : Prop :=
  ∀ t, o (deepRewrite t) = o t

/-- Extensional observables are rewrite-invariant. -/
theorem Extensional.rewriteInvariant {State : Type*} [DynSemiring State]
    {O : Type*} {o : Term → O} (h : Extensional State o) :
    RewriteInvariant o := by
  obtain ⟨oS, ho⟩ := h
  intro t
  rw [ho, ho, deepRewrite_eval]

/-! ## Part 5: Strictness — Both Inclusions Are Proper

    extensional ⊊ rewrite-invariant ⊊ all observables.

    rootTag breaks rewrite invariance (the Leibniz rewrite changes
    root constructors — the original obstruction phenomenon, now
    placed on the observable side of the boundary). isF₀ is
    rewrite-invariant but not extensional: it distinguishes f₀ from
    compose(f₀, f₀), which every model identifies. -/

/-- The root constructor of a term, as a six-valued tag. -/
inductive RootTag where
  | f₀ | f₁ | z | compose | oplus | obs
  deriving DecidableEq, Repr

/-- Read the root constructor. The canonical intensional observable. -/
def rootTag : Term → RootTag
  | .f₀ => .f₀
  | .f₁ => .f₁
  | .z => .z
  | .compose _ _ => .compose
  | .oplus _ _ => .oplus
  | .obs _ => .obs

/-- The root constructor is not rewrite-invariant: the Leibniz
    rewrite turns the obs-rooted obs(f₂) into an oplus-rooted term. -/
theorem rootTag_not_rewriteInvariant : ¬ RewriteInvariant rootTag :=
  fun h => absurd (h (.obs t_f₂)) (by decide)

/-- The root constructor is not extensional, in any model. -/
theorem rootTag_not_extensional (State : Type*) [DynSemiring State] :
    ¬ Extensional State rootTag :=
  fun h => rootTag_not_rewriteInvariant h.rewriteInvariant

/-- The root constructor supports no bisimulation: the intensional
    side of the boundary. -/
theorem rootTag_no_bisim (State : Type*) [DynSemiring State] :
    ¬ SupportsBisim State rootTag :=
  fun h => rootTag_not_extensional State
    ((supportsBisim_iff_extensional State rootTag).mp h)

/-- The witness pair: compose(f₀, f₀) and f₀ evaluate equally in
    EVERY model — this is the identity axiom A2, not a property of
    a particular semantics. -/
theorem eval_compose_f₀_f₀ {State : Type*} [DynSemiring State] :
    eval (.compose .f₀ .f₀) = (eval .f₀ : State) := by
  simp only [eval]
  exact compose_f₀ _

/-- The Leibniz rewrite of an observation never produces bare f₀:
    its outputs are oplus-rooted, f₁, z, or obs-rooted. -/
theorem obsRewrite_obs_ne_f₀ (u : Term) : obsRewrite (.obs u) ≠ .f₀ := by
  cases u <;> simp [obsRewrite]

/-- f₀ is the only term that normalizes to f₀. -/
theorem deepRewrite_eq_f₀_iff (t : Term) :
    deepRewrite t = .f₀ ↔ t = .f₀ := by
  cases t with
  | obs u =>
    simp only [deepRewrite]
    simp [obsRewrite_obs_ne_f₀ (deepRewrite u)]
  | f₀ => simp [deepRewrite]
  | f₁ => simp [deepRewrite]
  | z => simp [deepRewrite]
  | compose a b => simp [deepRewrite]
  | oplus a b => simp [deepRewrite]

/-- Syntactic equality with f₀, as a Boolean observable. -/
def isF₀ : Term → Bool := fun t => decide (t = .f₀)

/-- isF₀ is rewrite-invariant: normalization neither creates nor
    destroys bare f₀. -/
theorem isF₀_rewriteInvariant : RewriteInvariant isF₀ := fun t =>
  decide_eq_decide.mpr (deepRewrite_eq_f₀_iff t)

/-- isF₀ is NOT extensional: it separates f₀ from compose(f₀, f₀),
    which every model identifies. -/
theorem isF₀_not_extensional (State : Type*) [DynSemiring State] :
    ¬ Extensional State isF₀ := by
  rintro ⟨oS, ho⟩
  have h2 : isF₀ (.compose .f₀ .f₀) = isF₀ .f₀ := by
    rw [ho (.compose .f₀ .f₀), ho .f₀, eval_compose_f₀_f₀]
  exact absurd h2 (by decide)

/-- **STRICTNESS (Tier 2):** there is a rewrite-invariant observable
    that is not extensional. Together with rootTag, this gives
    extensional ⊊ rewrite-invariant ⊊ all observables. -/
theorem rewriteInvariant_not_extensional_exists
    (State : Type*) [DynSemiring State] :
    ∃ o : Term → Bool, RewriteInvariant o ∧ ¬ Extensional State o :=
  ⟨isF₀, isF₀_rewriteInvariant, isF₀_not_extensional State⟩

/-! ## Part 6: Injectivity Is Intensionality

    An injective code separates EVERY pair of distinct terms — in
    particular pairs the semantics identifies. So no injective code
    is extensional, and by the characterization, no injective code
    supports a bisimulation.

    Relation to no_coalgebra_morphism (Main.lean): that theorem says
    an injective ε cannot commute with one Leibniz step; this one
    says ε cannot support ANY bisimulation with the semantics, and
    locates the reason — injectivity puts ε on the intensional side
    of the extensionality boundary. The two statements are logically
    independent; this is the reinterpretation that gives the
    obstruction its content: the obstruction was never about codes
    failing to be clever enough. A faithful code is the maximally
    intensional observable, and the boundary excludes every
    intensional observable, with the faithful code as the extreme
    case. -/

/-- No injective coding of terms is extensional. -/
theorem injective_not_extensional {State : Type*} [DynSemiring State]
    (ε : Term → ℕ) (hε : Function.Injective ε) :
    ¬ Extensional State ε := by
  rintro ⟨oS, ho⟩
  have h2 : ε (.compose .f₀ .f₀) = ε .f₀ := by
    rw [ho (.compose .f₀ .f₀), ho .f₀, eval_compose_f₀_f₀]
  exact absurd (hε h2) (by decide)

/-- **INJECTIVITY IS INTENSIONALITY (Tier 2):**
    no injective coding supports a bisimulation with the semantics. -/
theorem injective_no_bisim {State : Type*} [DynSemiring State]
    (ε : Term → ℕ) (hε : Function.Injective ε) :
    ¬ SupportsBisim State ε :=
  fun h => injective_not_extensional ε hε
    ((supportsBisim_iff_extensional State ε).mp h)

/-! ## Part 7: Summary

    PROVED (sorry-free, no axioms):

    | Theorem | Content |
    |---------|---------|
    | synStep_eval | The syntactic step implements obs through eval |
    | evalGraphBisim (+ total) | The eval graph is a bisimulation |
    | codeBisim (+ total) | The eval-quote square commutes up to bisimulation |
    | supportsBisim_iff_extensional | Bisimulation support ⟺ extensionality |
    | Extensional.eval_congr | Extensional observables respect eval |
    | Extensional.rewriteInvariant | Extensional ⟹ rewrite-invariant |
    | rootTag_not_rewriteInvariant | Root constructor is not rewrite-invariant |
    | rootTag_no_bisim | The intensional witness |
    | deepRewrite_eq_f₀_iff | f₀ is the unique normalizer to f₀ |
    | isF₀_rewriteInvariant, isF₀_not_extensional | The middle witness |
    | rewriteInvariant_not_extensional_exists | Both inclusions strict |
    | injective_not_extensional, injective_no_bisim | Injectivity is intensionality |

    ANSWER TO THE EVAL-QUOTE QUESTION, AS OF THIS FILE:

    The square commutes up to bisimulation precisely for extensional
    observations. The encoding obstruction is the intensional side of
    that boundary, with injective codes as the extreme point. What
    remains open (Tier 3) is the quantitative version on a common
    carrier: whether primitive recursive code dynamics can be
    bisimilar to the semantic dynamics when the OUTPUTS themselves
    are codes — the growth-rate conjecture. -/

end SpectralMonoid
