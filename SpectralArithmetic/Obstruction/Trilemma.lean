/-
  The Encoding Trilemma, Resolved (Issue #68)
  ===========================================

  The standalone extraction repo (suisuss/Obstruction) claims an
  encoding trilemma — injectivity, homomorphism, non-trivial
  semantics: any two are compatible, all three impossible — but
  formalizes only two corners as separate lemmas. This file states
  and resolves the trilemma as theorems, in the universal setting
  of UniversalBisimulation.lean (every signature C, every Leibniz
  algebra), and shows it factors through the bisimulation boundary.

  Results (all sorry-free, no axioms):

  1. Freeness: TermF C is free on its signature — any homomorphic
     encoding into a Leibniz algebra equals eval (hom_eq_eval).
  2. Non-triviality is a THEOREM, not a hypothesis: the universal
     witness pair (a term and its Leibniz rewrite) is distinct but
     eval-equal in every algebra, so every Leibniz algebra over an
     inhabited term language has non-trivial semantics
     (nontrivialSemantics_of_term).
  3. The trilemma as one theorem (encoding_trilemma), and its
     sharpening: because of 2, the injective+homomorphic cell is
     inhabited EXACTLY by empty term algebras
     (exists_injective_homomorphism_iff) — the trilemma collapses
     to a dilemma (no_injective_homomorphism) once a single term
     exists.
  4. The two non-empty cells witnessed: eval realizes homomorphic +
     non-trivial (corner_homomorphic_nontrivial); a Godel coding of
     PA terms realizes injective + non-trivial
     (corner_injective_nontrivial).
  5. The crux: the dilemma is a corollary of the boundary theorem.
     Homomorphic encodings are extensional, hence support a
     bisimulation (Homomorphic.supportsBisimF); injective encodings
     support none, into any codomain (injective_no_bisim'); the
     boundary makes the sides disjoint
     (no_injective_homomorphism_via_boundary).
  6. The compression reading: extensionality is a kernel-order
     statement — o factors through eval iff ker(eval) ⊆ ker(o)
     (extensionalF_iff_ker_le), so the boundary says an observable
     supports a bisimulation iff it compresses at least as much as
     the semantics (supportsBisimF_iff_ker_le). Homomorphic
     encodings are the exact semantic compression, injective ones
     are lossless, and the dilemma is: no lossless compression to
     the semantic quotient (no_lossless_semantic_compression).
-/

import SpectralArithmetic.Obstruction.UniversalBisimulation

namespace UniversalObstruction

namespace TermF

variable {C : Type*} {S : Type*} {O : Type*}

/-! ## Part 1: The Three Properties -/

/-- An encoding is homomorphic for an algebra A when it interprets
    every constructor by A's corresponding operation — the sense in
    which "the encoding respects the operations". -/
structure Homomorphic (A : LeibnizAlgebra C S) (ε : TermF C → S) : Prop where
  const_eq : ∀ c, ε (.const c) = A.interpConst c
  comp_eq : ∀ a b, ε (.comp a b) = A.interpComp (ε a) (ε b)
  add_eq : ∀ a b, ε (.add a b) = A.interpAdd (ε a) (ε b)
  obs_eq : ∀ t, ε (.obs t) = A.interpObs (ε t)

/-- A semantics is non-trivial when two distinct terms share a
    meaning. -/
def NontrivialSemantics (A : LeibnizAlgebra C S) : Prop :=
  ∃ t₁ t₂ : TermF C, t₁ ≠ t₂ ∧ eval A t₁ = eval A t₂

/-- Evaluation itself is homomorphic. -/
theorem eval_homomorphic (A : LeibnizAlgebra C S) : Homomorphic A (eval A) :=
  ⟨fun _ => rfl, fun _ _ => rfl, fun _ _ => rfl, fun _ => rfl⟩

/-- **FREENESS:** TermF C is free on its signature, so eval is the
    unique homomorphism into any algebra. -/
theorem Homomorphic.eq_eval {A : LeibnizAlgebra C S} {ε : TermF C → S}
    (h : Homomorphic A ε) : ∀ t, ε t = eval A t := by
  intro t
  induction t with
  | const c => exact h.const_eq c
  | comp _ _ iha ihb => rw [h.comp_eq, iha, ihb]; rfl
  | add _ _ iha ihb => rw [h.add_eq, iha, ihb]; rfl
  | obs _ ih => rw [h.obs_eq, ih]; rfl

/-! ## Part 2: Non-Triviality Is Free

    In the Leibniz setting the third leg of the trilemma is not a
    hypothesis about the system: the universal witness pair — a
    compound observation and its Leibniz rewrite — is syntactically
    distinct (leibniz_changes_form) yet eval-equal in EVERY algebra
    (leibnizRewrite_preserves_eval). One term suffices to build it. -/

/-- **NON-TRIVIALITY IS A THEOREM:** every Leibniz algebra over an
    inhabited term language has non-trivial semantics. -/
theorem nontrivialSemantics_of_term (A : LeibnizAlgebra C S) (t₀ : TermF C) :
    NontrivialSemantics A :=
  ⟨leibnizRewrite (.obs (.comp t₀ t₀)), .obs (.comp t₀ t₀),
   leibniz_changes_form t₀ t₀, leibnizRewrite_preserves_eval A t₀ t₀⟩

/-! ## Part 3: The Trilemma and Its Collapse -/

/-- **THE THIRD CELL (general form):** an injective homomorphism
    forces the semantics itself to be injective — no two distinct
    terms can share a meaning. -/
theorem eval_injective_of_injective_hom {A : LeibnizAlgebra C S}
    {ε : TermF C → S} (hinj : Function.Injective ε)
    (hhom : Homomorphic A ε) : Function.Injective (eval A) :=
  funext hhom.eq_eval ▸ hinj

/-- **THE ENCODING TRILEMMA:** no encoding into a Leibniz algebra is
    simultaneously injective and homomorphic while the semantics is
    non-trivial. -/
theorem encoding_trilemma (A : LeibnizAlgebra C S) (ε : TermF C → S) :
    ¬(Function.Injective ε ∧ Homomorphic A ε ∧ NontrivialSemantics A) := by
  rintro ⟨hinj, hhom, t₁, t₂, hne, heq⟩
  exact hne (eval_injective_of_injective_hom hinj hhom heq)

/-- **THE TRILEMMA COLLAPSES TO A DILEMMA:** non-triviality being
    automatic, injective + homomorphic is impossible outright once a
    single term exists. -/
theorem no_injective_homomorphism (A : LeibnizAlgebra C S) (t₀ : TermF C)
    (ε : TermF C → S) (hinj : Function.Injective ε)
    (hhom : Homomorphic A ε) : False :=
  encoding_trilemma A ε ⟨hinj, hhom, nontrivialSemantics_of_term A t₀⟩

/-! ## Part 4: Sharpness — Every Cell Characterized -/

instance instIsEmpty [IsEmpty C] : IsEmpty (TermF C) where
  false t := by
    induction t with
    | const c => exact isEmptyElim c
    | comp _ _ iha _ => exact iha
    | add _ _ iha _ => exact iha
    | obs _ ih => exact ih

/-- **THE INJECTIVE + HOMOMORPHIC CELL IS EXACTLY THE EMPTY TERM
    ALGEBRAS:** an injective homomorphism into A exists iff there are
    no terms at all. This is sharper than the extraction repo's
    "only works for trivial systems": in the Leibniz setting the
    Leibniz rule itself manufactures a non-trivial identification, so
    the only escape is having nothing to encode. -/
theorem exists_injective_homomorphism_iff (A : LeibnizAlgebra C S) :
    (∃ ε : TermF C → S, Function.Injective ε ∧ Homomorphic A ε) ↔
      IsEmpty (TermF C) := by
  constructor
  · rintro ⟨ε, hinj, hhom⟩
    exact ⟨fun t₀ => no_injective_homomorphism A t₀ ε hinj hhom⟩
  · intro h
    exact ⟨eval A, fun a _ _ => isEmptyElim a, eval_homomorphic A⟩

/-- **CORNER WITNESS (homomorphic + non-trivial, not injective):**
    eval realizes it in every algebra with a term. -/
theorem corner_homomorphic_nontrivial (A : LeibnizAlgebra C S)
    (t₀ : TermF C) :
    Homomorphic A (eval A) ∧ NontrivialSemantics A ∧
      ¬Function.Injective (eval A) := by
  refine ⟨eval_homomorphic A, nontrivialSemantics_of_term A t₀, fun hinj => ?_⟩
  obtain ⟨t₁, t₂, hne, heq⟩ := nontrivialSemantics_of_term A t₀
  exact hne (hinj heq)

deriving instance Countable for PAConst
deriving instance Countable for TermF

/-- A non-trivial Leibniz algebra on ℕ: multiplication, addition, the
    zero derivation. -/
def natAlgebra : LeibnizAlgebra PAConst ℕ where
  interpConst _ := 0
  interpComp := (· * ·)
  interpAdd := (· + ·)
  interpObs _ := 0
  leibniz_law a b := by simp

/-- **CORNER WITNESS (injective + non-trivial, not homomorphic):** a
    Godel coding of PA terms into the natural-number algebra. The
    coding exists by countability; the trilemma then forces it to be
    non-homomorphic. -/
theorem corner_injective_nontrivial :
    ∃ ε : TermF PAConst → ℕ, Function.Injective ε ∧
      NontrivialSemantics natAlgebra ∧ ¬Homomorphic natAlgebra ε := by
  obtain ⟨ε, hε⟩ := Countable.exists_injective_nat (TermF PAConst)
  exact ⟨ε, hε, nontrivialSemantics_of_term _ (.const .zero), fun hhom =>
    no_injective_homomorphism _ (.const .zero) ε hε hhom⟩

/-! ## Part 5: The Trilemma Is a Corollary of the Boundary

    The boundary theorem (supportsBisimF_iff_extensionalF) already
    contains the trilemma: homomorphic encodings factor through eval
    (via the identity output map), so they sit on the extensional
    side and support a bisimulation; injective encodings are
    maximally intensional and support none. The dilemma is the
    disjointness of the two sides. -/

/-- Homomorphic encodings are extensional. -/
theorem Homomorphic.extensionalF {A : LeibnizAlgebra C S} {ε : TermF C → S}
    (h : Homomorphic A ε) : ExtensionalF A ε :=
  ⟨id, h.eq_eval⟩

/-- Homomorphic encodings support a bisimulation with the semantics
    (the boundary theorem's extensional direction). -/
theorem Homomorphic.supportsBisimF {A : LeibnizAlgebra C S}
    {ε : TermF C → S} (h : Homomorphic A ε) : SupportsBisimF A ε :=
  (supportsBisimF_iff_extensionalF A ε).mpr h.extensionalF

/-- Injectivity excludes extensionality into ANY codomain — the
    ℕ-valued injective_not_extensionalF, codomain-generalized. -/
theorem injective_not_extensional (A : LeibnizAlgebra C S) (t₀ : TermF C)
    {ε : TermF C → O} (hε : Function.Injective ε) : ¬ExtensionalF A ε :=
  fun h => leibniz_changes_form t₀ t₀
    (hε (h.eval_congr (leibnizRewrite_preserves_eval A t₀ t₀)))

/-- No injective coding into any codomain supports a bisimulation. -/
theorem injective_no_bisim' (A : LeibnizAlgebra C S) (t₀ : TermF C)
    {ε : TermF C → O} (hε : Function.Injective ε) : ¬SupportsBisimF A ε :=
  fun h => injective_not_extensional A t₀ hε
    ((supportsBisimF_iff_extensionalF A ε).mp h)

/-- **THE DILEMMA VIA THE BOUNDARY:** a homomorphic encoding supports
    a bisimulation, an injective one supports none — both directions
    of the boundary theorem, nothing else. The trilemma is a
    corollary of the bisimulation boundary. -/
theorem no_injective_homomorphism_via_boundary (A : LeibnizAlgebra C S)
    (t₀ : TermF C) (ε : TermF C → S) (hinj : Function.Injective ε)
    (hhom : Homomorphic A ε) : False :=
  injective_no_bisim' A t₀ hinj hhom.supportsBisimF

/-! ## Part 6: The Compression Reading

    ExtensionalF is a kernel-order statement in disguise: o factors
    through eval exactly when o identifies whatever eval identifies.
    Read the kernel of an observable as the compression it performs —
    which distinctions it discards. Then extensional observables are
    those that compress at least as much as the semantics, a
    homomorphic encoding is the exact semantic compression (the
    quotient map), an injective encoding is lossless, and the dilemma
    says lossless compression to the semantic quotient is impossible
    because the Leibniz rule keeps the quotient non-trivial. -/

/-- The kernel of an observable: the pairs it identifies — the
    compression it performs. -/
def Ker (o : TermF C → O) (t₁ t₂ : TermF C) : Prop :=
  o t₁ = o t₂

/-- **EXTENSIONALITY IS COMPRESSION DOMINANCE:** an observable is
    extensional iff its kernel contains eval's kernel — iff it
    compresses at least as much as the semantics does. -/
theorem extensionalF_iff_ker_le (A : LeibnizAlgebra C S) (t₀ : TermF C)
    (o : TermF C → O) :
    ExtensionalF A o ↔ ∀ t₁ t₂, Ker (eval A) t₁ t₂ → Ker o t₁ t₂ := by
  classical
  constructor
  · intro h t₁ t₂ hk
    exact h.eval_congr hk
  · intro h
    refine ⟨fun s => if hs : ∃ t, eval A t = s then o hs.choose else o t₀,
      fun t => ?_⟩
    have hex : ∃ t', eval A t' = eval A t := ⟨t, rfl⟩
    simp only [dif_pos hex]
    exact (h _ _ hex.choose_spec).symm

/-- **THE BOUNDARY IS A COMPRESSION STATEMENT:** an observable
    supports a bisimulation with the semantics iff it compresses at
    least as much as eval. -/
theorem supportsBisimF_iff_ker_le (A : LeibnizAlgebra C S) (t₀ : TermF C)
    (o : TermF C → O) :
    SupportsBisimF A o ↔ ∀ t₁ t₂, Ker (eval A) t₁ t₂ → Ker o t₁ t₂ :=
  (supportsBisimF_iff_extensionalF A o).trans
    (extensionalF_iff_ker_le A t₀ o)

/-- A homomorphic encoding is the EXACT semantic compression: its
    kernel is eval's kernel. -/
theorem Homomorphic.ker_iff {A : LeibnizAlgebra C S} {ε : TermF C → S}
    (h : Homomorphic A ε) (t₁ t₂ : TermF C) :
    Ker ε t₁ t₂ ↔ Ker (eval A) t₁ t₂ := by
  unfold Ker
  rw [h.eq_eval t₁, h.eq_eval t₂]

/-- An injective encoding is LOSSLESS: its kernel is equality. -/
theorem injective_ker_iff {ε : TermF C → O} (hε : Function.Injective ε)
    (t₁ t₂ : TermF C) : Ker ε t₁ t₂ ↔ t₁ = t₂ :=
  ⟨fun h => hε h, fun h => congrArg ε h⟩

/-- **NO LOSSLESS COMPRESSION TO THE SEMANTIC QUOTIENT:** the dilemma
    in compression vocabulary. eval's kernel is non-trivial in every
    algebra (the universal witness pair), so no lossless encoding —
    into any codomain — can dominate it. -/
theorem no_lossless_semantic_compression (A : LeibnizAlgebra C S)
    (t₀ : TermF C) {ε : TermF C → O} (hε : Function.Injective ε)
    (hdom : ∀ t₁ t₂, Ker (eval A) t₁ t₂ → Ker ε t₁ t₂) : False :=
  leibniz_changes_form t₀ t₀
    (hε (hdom _ _ (leibnizRewrite_preserves_eval A t₀ t₀)))

/-! ## Part 7: Summary

    PROVED (sorry-free, no axioms), universally over all signatures C
    and all Leibniz algebras:

    | Theorem | Content |
    |---------|---------|
    | Homomorphic.eq_eval | Freeness: homomorphic means eval |
    | nontrivialSemantics_of_term | Non-triviality is automatic |
    | encoding_trilemma | The trilemma as one theorem |
    | no_injective_homomorphism | Its collapse to a dilemma |
    | exists_injective_homomorphism_iff | Third cell = empty algebras, exactly |
    | corner_homomorphic_nontrivial | Cell witness: eval |
    | corner_injective_nontrivial | Cell witness: Godel coding of PA terms |
    | Homomorphic.supportsBisimF | Homomorphic is extensional-side |
    | injective_no_bisim' | Injective is intensional-side, any codomain |
    | no_injective_homomorphism_via_boundary | The trilemma factors through the boundary |
    | extensionalF_iff_ker_le | Extensional = compresses at least as much as eval |
    | supportsBisimF_iff_ker_le | The boundary as a compression statement |
    | Homomorphic.ker_iff | Homomorphic = the exact semantic compression |
    | injective_ker_iff | Injective = lossless |
    | no_lossless_semantic_compression | The dilemma in compression vocabulary |

    Resolution of the extraction repo's claim: the trilemma is true
    but understated. Non-trivial semantics is not an assumption to
    trade off against the other two properties — the Leibniz rule
    manufactures it from any single term. The "pick two" table's
    injective+homomorphic row is inhabited only by term algebras with
    no terms; the other two rows have genuine witnesses. And the
    whole configuration is the bisimulation boundary restricted to
    encodings: homomorphism places a code on the extensional side,
    injectivity on the intensional side, and the boundary theorem
    keeps them apart. -/

end TermF

end UniversalObstruction
