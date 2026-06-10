# Note: calculi for the "regime of encodings/rewrite rules" and the proof-search meta-move

Date: 2026-06-10. Conversation note, not a direction doc. Context: question was whether a
calculus exists for the regime of rewrite rules, encodings, substitution rules, instruction
sets — and whether proving "finding a solution to P vs NP is an NP problem" yields anything.

## The calculi exist

The regime is well-mapped:

- **Term rewriting systems / semi-Thue systems / Post canonical systems** — the general
  theory of substitution and rewrite rules. Mature (Knuth–Bendix, abstract reduction
  systems).
- **Descriptive complexity** — complexity classes characterized purely by language/logic,
  no machines: Fagin's theorem says NP = existential second-order logic; P = FO +
  least-fixed-point (on ordered structures). The cleanest "calculus of encoding and
  expression."
- **Implicit computational complexity** — calculi whose typable terms are exactly the
  poly-time functions (Bellantoni–Cook, light linear logic). P itself, captured as syntax.
- **Bounded arithmetic and proof complexity** (Cook's PV, Buss's S^1_2, Krajicek's
  program) — formal systems whose provable statements are exactly those with "feasible"
  proofs. The calculus of how problems get solved by reasoning; the one the meta-move
  actually needs.

## The inference, and where it breaks

"Finding a solution to P vs NP is an NP problem" is trivially true and uninformative. For
any formal system, "does statement phi have a proof of length <= n?" is in NP (guess the
proof, verify in poly time); it is NP-complete in general. So proof-search for P != NP is
an NP problem — but so is proof-search for the Riemann Hypothesis and for 2+2=4. The
statement carries no information about P vs NP specifically.

Worse, the desired conclusion is circular: "the meta-problem is NP-hard, therefore solving
P vs NP is infeasible" only follows if NP-hard problems are actually infeasible — which is
the very thing in question. If P = NP, then NP-hard proof search is easy and the
meta-argument evaporates. A resolution of P vs NP cannot be extracted from the complexity
of searching for its own proof; the statement is consistent with both answers.

## The salvageable version

The non-circular form of the intuition: prove limitation theorems about classes of
solution-techniques, formalized as calculi. That is exactly what the three barriers are:

- **Relativization** — a limitation theorem about diagonalization-style arguments.
- **Natural proofs** — a limitation theorem (conditional on PRGs) about a formalized class
  of combinatorial lower-bound techniques.
- **Razborov's unprovability results** — circuit lower bounds are unprovable in certain
  bounded-arithmetic theories, under crypto assumptions: "P != NP cannot be solved within
  this calculus of feasible reasoning."

The self-referential flavor has a folklore form with substance: if P = NP, then short
proofs are easy to find, so the fact that nobody has found a proof of P = NP is weak
evidence against it — and Razborov–Rudich has the genuinely strange property that the
hardness of proving hardness is itself a consequence of hardness. Aaronson's "Is P vs NP
formally independent?" survey covers this terrain; Krajicek's proof-complexity-generators
program is the serious ongoing attempt.

## Project-specific notes

1. This is essentially what Part 2 of the thesis already is. The universal encoding
   obstruction — a theorem quantifying over all signatures/encodings satisfying certain
   axioms — is a barrier-type result about the regime of encodings, not a resolution of
   P vs NP. The honest framing of the idea is "another barrier theorem"; the
   NaturalProofsEvasion and bisimulation work is the right vehicle for it.
2. The endpoint the sketch points at — "therefore P vs NP is unresolvable / independent" —
   is the direction `docs/theory/direction/focus.md` explicitly rules out as a
   deliverable: proving independence from ZFC is far beyond current technology, and the
   weaker "unprovable in bounded arithmetic" is Razborov's territory with crypto
   assumptions attached.

## Bottom line

The calculus exists (several do); the meta-move is legitimate as a barrier theorem about
formalized technique-classes; but the specific inference "proof search is NP, therefore a
conclusion about P vs NP" gives nothing — it is true of every mathematical statement and
circular at the point where it would be cashed out.
