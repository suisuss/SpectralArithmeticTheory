# Positioning: Learning Certificate vs PR/SDCL

## Date: 2026-03-31

## Purpose

Due diligence on the "learning certificate" concept — the minimum set of clauses that, when added to a formula, makes UP sufficient to derive the empty clause. This document positions our work relative to existing proof systems, particularly Heule/Kiesl/Biere's work on propagation redundancy (PR) and satisfaction-driven clause learning (SDCL).

---

## 1. The Proof System Hierarchy

Modern SAT proof systems form a strict hierarchy:

```
RUP ⊂ RAT ⊂ SPR ⊂ PR ⊂ SR
```

- **RUP** (Reverse Unit Propagation): clause C can be added if F AND NOT(C) derives empty clause via UP
- **RAT** (Resolution Asymmetric Tautology): generalizes RUP with resolution on a pivot literal
- **SPR** (Subset Propagation Redundancy): clause C is redundant if there exists a witness assignment omega such that F restricted to alpha (the assignment blocked by C) UP-derives F restricted to omega
- **PR** (Propagation Redundancy): further generalizes SPR
- **SR** (Substitution Redundancy): most general, subsumes all the above

With new variables allowed, all these systems are polynomially equivalent to extended resolution. Without new variables, the hierarchy is strict.

Key result (Heule, Kiesl, Biere 2019): SDCL can produce polynomial-size proofs for pigeonhole, Tseitin, and mutilated chessboard — all formulas that require exponential resolution proofs. CDCL is limited to resolution power.

Source: [Encoding Redundancy for Satisfaction-Driven Clause Learning](https://link.springer.com/chapter/10.1007/978-3-030-17462-0_3), [DRAT Proofs, Propagation Redundancy, and Extended Resolution](https://link.springer.com/chapter/10.1007/978-3-030-24258-9_5)

---

## 2. What a "Learning Certificate" Actually Is

Our "learning certificate" — k clauses that make UP sufficient — is a specific instance of this hierarchy:

**A learning certificate is a set of clauses {C1, ..., Ck} such that F + {C1, ..., Ck} derives the empty clause via unit propagation alone.**

In proof complexity terms, this is a **RUP proof** reorganized as a set of lemmas. The verification is: add the clauses, run UP, check for empty clause. This IS the RUP verification procedure.

Specifically:
- Each clause Ci in the certificate must be a consequence of F (otherwise adding it changes satisfiability)
- The clauses are ordered so that after adding all of them, UP cascades to empty clause
- The verification is polynomial: O(|F| + k) for UP on the augmented formula

**This is not new as a proof format.** RUP has been the standard UNSAT certificate format since the SAT competition started requiring proofs. DRAT (deletion + RAT) is the current standard.

---

## 3. What IS New: The Dynamic Measurement

The proof FORMAT is known. What's new in our work:

### 3.1. Contraction Ratio Trajectory

No existing solver or proof system measures "how much did the last batch of learned clauses simplify the formula" as a runtime signal. Our contraction ratio trajectory:

```
PHP(5,4): [100%, 100%, 105%, 1000%]
```

This is a DYNAMIC signal that shows the approach to critical mass. The PR/SDCL literature studies which clauses ARE propagation redundant, not WHEN during search the accumulated clauses cross the sufficiency threshold.

### 3.2. Width Trajectory as Phase Indicator

The width trajectory of learned clauses across rounds:

```
PHP(4,3): [3, 2, 1] → cascade at width 1
```

No existing solver reads the trajectory of learned clause widths as a signal for strategy switching. Existing solvers use LBD (literal block distance) as a clause quality metric, but LBD is per-clause, not a trajectory across rounds.

### 3.3. Promotion Ratio

Our finding: promotion ratio (fraction of clause literals that become UP-determinable when the clause is added) perfectly correlates with cascade breakthrough:

```
promo=0%  → no cascade (100% of learning-only rounds)
promo≥33% → cascade breakthrough (100% of solving rounds)
```

This is related to but distinct from propagation redundancy. A PR clause is one that CAN be added without changing satisfiability. A high-promotion clause is one that SHOULD be added because it triggers cascading inference. All PR clauses are valid additions; high-promotion PR clauses are USEFUL additions.

### 3.4. Adaptive Ordering

Our width trajectory signal determines when to use fixed vs permuted variable ordering. No existing solver makes this decision based on learned clause width trajectory. Existing restart strategies (Luby, glucose) are based on conflict counts or LBD averages, not on resolution width patterns.

---

## 4. Where Our System Sits in the Hierarchy

Our iterated 1-UIP pipeline operates at the **resolution** level — strictly weaker than SDCL/PR:

| System | Proof power | What it can solve |
|---|---|---|
| Resolution | Polynomial for some, exponential for PHP/Tseitin | What CDCL does |
| **Our iterated 1-UIP** | **Resolution + round-wise augmentation** | **PHP to p=6 in 15 rounds** |
| DRAT/RAT | Polynomially simulates extended resolution | Everything resolution can + more |
| SDCL/PR | Polynomially simulates extended resolution | PHP, Tseitin, mutilated chessboard in poly |

Our system is NOT more powerful than SDCL. SDCL produces PR clauses that are strictly stronger than resolution-derived clauses. Our 1-UIP produces resolution-derived clauses, just organized in rounds with augmentation.

However: our PHP(5,4) proof in 6 rounds with 90 learned clauses is comparable to SDCL's polynomial proofs for PHP. The proof structure is different (iterated resolution augmentation vs PR clause addition) but the outcome is the same.

---

## 5. The Honest Positioning

### What we should NOT claim:

- That the learning certificate is a new proof format (it's RUP)
- That our system is stronger than resolution (it isn't; it's resolution with clause accumulation)
- That the contraction ratio is a new proof complexity measure (it's a heuristic)

### What we CAN claim:

1. **The contraction ratio trajectory is a novel runtime signal** that no existing solver or proof system tracks. It predicts the learning-to-inference phase transition.

2. **The promotion ratio perfectly correlates with cascade breakthrough** — this is empirical data that connects clause quality (an existing concept) to cascade triggering (a new measurement).

3. **Width trajectory as ordering signal** — using resolution width patterns to decide between fixed and randomized variable ordering is new. It combines a proof complexity measure (width) with a solver engineering decision (ordering).

4. **The iterated pipeline** — learn, augment, cascade, repeat with adaptive ordering — is architecturally novel as a solver design, even though its proof-theoretic power is bounded by resolution.

5. **The crawl-contract loop with split escape** — signal-driven inprocessing where contraction ratio drives the crawl budget and stall detection triggers decomposition is a genuinely new solver architecture.

### What to investigate further:

- **Does LBD correlate with our width trajectory?** If width trajectory provides the same signal as LBD, it's redundant. If it captures something different, it's complementary.

- **Can we lift from resolution to PR?** If our 1-UIP were replaced with PR clause learning (SDCL-style), the iterated pipeline would be strictly stronger. The measurement infrastructure (contraction ratio, width trajectory, promotion ratio) would still apply.

- **Is the contraction ratio useful for SDCL solvers?** If a SDCL solver tracked our contraction ratio, would it make better decisions about when to switch between CDCL-style and SDCL-style learning?

---

## 6. Recommended Framing for Publication

The paper should NOT be framed as "a new proof system" or "a new certificate format." It should be framed as:

**"Signal-driven inprocessing: using contraction ratio, width trajectory, and promotion ratio as runtime signals for adaptive SAT solving."**

The contributions are:
1. The signals (measurable, novel)
2. The adaptive decisions they drive (ordering, budget, split)
3. The empirical validation (PHP, random, modular instances)
4. The architectural pattern (crawl-contract with split escape)

The proof complexity context (PR, SDCL, RUP) should be cited as the theoretical foundation that our SIGNALS operate within, not as something we improve upon.

---

## Sources

- [Encoding Redundancy for Satisfaction-Driven Clause Learning (Heule, Kiesl, Biere, TACAS 2019)](https://link.springer.com/chapter/10.1007/978-3-030-17462-0_3)
- [DRAT Proofs, Propagation Redundancy, and Extended Resolution (Buss, Thapen 2019)](https://link.springer.com/chapter/10.1007/978-3-030-24258-9_5)
- [DRAT and Propagation Redundancy Proofs Without New Variables (Buss, Thapen)](https://mathweb.ucsd.edu/~sbuss/ResearchWeb/DRAT_PR/)
- [Preprocessing of Propagation Redundant Clauses (Reeves, Heule 2022)](https://www.cs.cmu.edu/~mheule/publications/IJCAR22.pdf)
- [Strong Extension-Free Proof Systems (Heule, Kiesl, Biere)](https://www.cs.cmu.edu/~mheule/publications/pr_extres.pdf)
- [Pool Resolution and Its Relation to Regular Resolution and DPLL with Clause Learning (Van Gelder 2005)](https://link.springer.com/chapter/10.1007/11591191_40)
- [Proof Complexity and SAT Solving (Buss, Nordstrom)](https://mathweb.ucsd.edu/~sbuss/ResearchWeb/ProofComplexitySAT/ProofComplexityChapter.pdf)
- [Learning Shorter Redundant Clauses in SDCL Using MaxSAT (2023)](https://drops.dagstuhl.de/entities/document/10.4230/LIPIcs.SAT.2023.18)
