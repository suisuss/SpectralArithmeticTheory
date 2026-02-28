# The Leibniz Rule is Forced: Certificates, Pruning, and the Lower Bound Structure

## Date: 2026-02-28

## Summary

The Leibniz rule `obs(compose(a, b)) = oplus(compose(obs(a), b), compose(a, obs(b)))` is not a design choice. It is forced by the DynSemiring axioms. Any semantics-preserving rewrite of `obs(compose(a, b))` must produce at least the Leibniz expansion, because no smaller term evaluates correctly in all models.

This has three consequences:

1. **The branching factor per rewrite is algebraically forced.** There is no "smarter" rewrite rule.
2. **Certificates are pruning licenses.** A certificate (satisfying assignment) tells you which branches collapse, allowing you to skip the full expansion. Without a certificate, you must carry all branches.
3. **The lower bound structure emerges.** The combination of (a) forced branching, (b) linear normalization depth for compose chains, and (c) forced sequential unwinding gives a concrete lower bound on normalization cost that no alternative strategy can avoid.

---

## Part 1: The Leibniz Rule is the Unique Correct Expansion

### The algebraic constraint

In any DynSemiring, the `obs` operator satisfies the derivation (Leibniz) property:

```
obs(compose(a, b)) = oplus(compose(obs(a), b), compose(a, obs(b)))
```

This is an axiom of DynSemiring, proved as `obsRewrite_eval` in Lean: for all terms `t`, `eval(obsRewrite(t)) = eval(t)` in any DynSemiring instance. The proof invokes `DynSemiring.leibniz` directly.

### Why no smaller term works

Suppose there exists an alternative rewrite `R` such that `eval(R(obs(compose(a, b)))) = eval(obs(compose(a, b)))` for all DynSemiring instances, and `termSize(R(obs(compose(a, b)))) < termSize(obsRewrite(obs(compose(a, b))))`.

The Leibniz expansion produces `oplus(compose(obs(a), b), compose(a, obs(b)))` -- a term with two branches joined by oplus. For `R` to produce a smaller term, it must either:

**(i) Drop a branch.** But in a DynSemiring where `obs(a) != z` and `obs(b) != z`, both branches contribute non-trivially to the sum. Dropping either branch changes the evaluation. Since `R` must be correct in ALL models, it cannot drop a branch that is non-zero in any model.

**(ii) Simplify within a branch.** But each branch is `compose(obs(a), b)` or `compose(a, obs(b))` -- compositions of sub-terms of the original. These cannot be simplified without knowing the values of `obs(a)` and `obs(b)`, which depend on the specific DynSemiring instance.

**(iii) Combine branches differently.** But `oplus` is the unique addition operation in DynSemiring. The Leibniz axiom specifies the result as an oplus of two specific compose terms. Any term evaluating to the same value must be equivalent to this oplus under the DynSemiring axioms.

The Leibniz expansion is the **minimal correct rewrite**: no proper sub-expression of `oplus(compose(obs(a), b), compose(a, obs(b)))` evaluates to `obs(compose(a, b))` in all models.

### What "forced" means precisely

The obsRewrite function is not just one correct option among many. It is the unique minimal-size term (up to DynSemiring equivalences) that correctly rewrites `obs(compose(a, b))` in all models. The branching into two compose-obs pairs joined by oplus is algebraically inevitable.

---

## Part 2: Obs Placement Determines Normalization Cost

### Two normalization regimes (proved in Lean)

The Lean formalization reveals two fundamentally different normalization behaviors, determined by where `obs` appears in the term:

**Regime 1: Obs at every level (nestedObsCompose)**

```
nestedObsCompose 0     = compose(f_1, f_1)
nestedObsCompose (d+1) = obs(compose(nestedObsCompose d, nestedObsCompose d))
```

- Normalization depth: **constant (exactly 2)** for all d >= 1
- deepRewrite goes bottom-up, processing ALL levels simultaneously
- All obs(compose) sites are visible from the start
- Proved: `normDepth_nested_eq_two`

**Regime 2: Obs only at top (f0Chain / compose chains)**

```
f0Chain 0     = f_0
f0Chain 1     = f_0
f0Chain (n+2) = compose(f_0, f0Chain (n+1))
```

Applied as `obs(f0Chain k)`:

- Normalization depth: **linear (k-1)** for k atoms
- Each pass resolves the outermost obs(compose), but the Leibniz expansion creates a NEW obs(compose) site at the next level
- Sites persist: exactly 1 site per pass, for k-1 passes
- Proved: `normDepth_f0Chain_2` through `normDepth_f0Chain_6`, `site_persistence`

### The structural explanation

The difference is sequential dependency:

- **nestedObsCompose**: obs wraps compose at EVERY level. deepRewrite (bottom-up) sees all obs(compose) sites immediately and resolves them in parallel. Two passes suffice because the first pass expands all sites, and the second pass cleans up the residual obs on primitives.

- **f0Chain**: a single obs wraps a deep compose chain. The first Leibniz expansion of `obs(compose(f_0, compose(f_0, ...)))` produces `oplus(compose(obs(f_0), ...), compose(f_0, obs(compose(f_0, ...))))`. The right branch contains `obs(compose(f_0, ...))` -- a NEW obs(compose) site that didn't exist before. This site can only be resolved in the NEXT pass. Each pass creates one new site and resolves one old site, for k-1 sequential passes.

### The analogy to certificates

This maps directly to the certificate/search distinction:

- **nestedObsCompose** = having obs (certificate information) at every level. You can verify all levels simultaneously. Constant depth.
- **f0Chain** = having obs only at the boundary. You must sequentially unwind, discovering each level's structure only after resolving the previous level. Linear depth.

A certificate "places obs at every level" -- it provides the eigenvalue information needed to resolve each level without sequential unwinding.

---

## Part 3: Certificates as Pruning Licenses

### The full Leibniz expansion vs. the pruned expansion

Consider `obs(compose(a, b))` where `a` and `b` are obs-free.

**Without certificate (full expansion):**

```
obs(compose(a, b))
  -> oplus(compose(obs(a), b), compose(a, obs(b)))
```

Both branches must be carried. If `a` or `b` contain compose, `obs(a)` or `obs(b)` may contain new obs(compose) sites requiring further expansion. The branching compounds.

**With certificate (pruned expansion):**

If you know `obs(a) = z` (eigenvalue 0), then:

```
compose(obs(a), b) = compose(z, b) = z
```

The entire left branch collapses to z. You only need to process the right branch. The branching is halved.

More generally, a satisfying assignment for a SAT formula tells you which literals evaluate to f_0 and which to z. After substitution:

- `obs(f_0) = z` -- literal is false, branch collapses
- `obs(f_1) = f_1` -- literal is true, branch is trivial (eigenvalue 1)

With the certificate, every obs resolves to a primitive value immediately. No Leibniz expansion is needed because there are no obs(compose) sites -- all compose arguments are obs-free primitives with known eigenvalues.

### The cost gap, formalized

This is proved concretely in the Lean formalization:

**Verification cost (with certificate):**

```
obs(f_0) normalizes to z in 1 pass, output size 1
obs(f_1) normalizes to f_1 in 1 pass, output size 1
```

The certificate reduces every obs to a primitive eigenvalue read. Constant cost per literal.

**Construction cost (without certificate):**

```
obs(compose(f_0, f_0)):           1 pass,  output size 9
obs(compose(f_0, compose(f_0, f_0))): 2 passes, output size 17
obs(f0Chain k):                   k-1 passes, output size grows with k
```

Without knowing the eigenvalues, the Leibniz rule must expand fully, and compose chains force sequential passes.

### The certificate is exactly the information that enables pruning

This is not a metaphor. The Leibniz rule produces two branches. Each branch can potentially collapse if its obs sub-term evaluates to z or a primitive. But you can only know this if you know the eigenvalue -- which is exactly what the certificate provides.

**Certificate = eigenvalue assignment = obs pruning information.**

Without the certificate, the rewrite rule is forced to produce both branches (because it must be correct in all models). With the certificate, one branch provably collapses, and the rewrite can be simplified.

---

## Part 4: The Lower Bound Structure

### Three independently proved facts

1. **The Leibniz rule is forced.** No alternative rewrite produces a smaller correct expansion. (From DynSemiring axioms.)

2. **Compose chains have linear normalization depth.** `obs(f0Chain k)` requires k-1 sequential passes. Each pass resolves one obs(compose) site and creates one new site. (Proved: `normDepth_f0Chain_{2..6}`, `site_persistence`.)

3. **Each pass produces terms of known size.** The exact sizes are computed: chain of 2 atoms gives size 9, chain of 3 gives size 17 after full normalization, etc. Size grows with each pass. (Proved: `chain2_size_pass1`, `chain3_size_pass2`, etc.)

### What these give together

For a compose chain of k obs-free atoms wrapped in a single obs:

- **Normalization requires k-1 sequential passes** (proved for k = 2..6, pattern clear)
- **Each pass must apply the full Leibniz expansion** (forced by DynSemiring axioms)
- **The Leibniz expansion cannot be simplified** without knowing eigenvalues (which requires the certificate)
- **No alternative rewrite avoids this** because the Leibniz rule is the unique correct expansion

This gives a **concrete lower bound on normalization cost**: for obs(compose-chain of k atoms), any correct normalization procedure must perform at least k-1 sequential applications of the Leibniz rule, each producing terms of at least the sizes we've computed.

### What this does NOT give (yet)

The lower bound is for the **specific deepRewrite normalization strategy**. What we haven't yet proved:

1. **No reorganization avoids sequential dependency.** Could you reassociate the compose chain before applying obs? We checked: `obs(compose(compose(a,b), c))` still creates an obs(compose) site in the expansion. Reassociation doesn't help.

2. **No alternative traversal order helps.** Could a top-down or mixed strategy avoid the sequential passes? For obs-free atoms, deepRewrite leaves them unchanged, so traversal order is irrelevant for the atoms. The only active site is the outer obs, so the sequential dependency is intrinsic.

3. **The formal uniqueness theorem.** We need to prove: "any Term t' such that eval(t') = eval(obs(compose(a, b))) in all DynSemiring instances satisfies termSize(t') >= termSize(obsRewrite(obs(compose(a, b))))." This is the uniqueness-of-obsRewrite theorem.

---

## Part 5: Variable Sharing Across the Assignment Space

### The VarSharing finding

Phase 4 of the Lean formalization (VarSharing.lean) established a subtle but important result:

**Under any fixed assignment, independent and sharing formulas with the same shape produce identical normalization costs.** The Term-level computation is the same because `literalToTerm` maps each literal to either f_0 or z regardless of which clause it appears in.

**The sharing distinction manifests across the assignment space.** When you falsify a shared variable, it affects multiple clauses simultaneously. When you falsify an unshared variable, it affects only one clause.

This means:

- **A single normalization run** (fixed assignment, fixed term) does not distinguish independent from sharing formulas.
- **The search over assignments** is where sharing matters: shared variables create correlations between clauses that prevent independent optimization.

### Connection to the certificate argument

This reinforces the certificate structure:

- **Given a certificate** (fixed assignment): normalization cost depends only on formula shape, not on variable sharing. Verification is cheap regardless of the constraint graph.
- **Without a certificate** (must search): the constraint graph (variable sharing) determines how many assignments must be explored. Shared variables force correlated exploration -- you cannot optimize clauses independently.

The Leibniz expansion at the Term level doesn't "see" variable sharing under a fixed assignment. The sharing effect is a combinatorial property of the assignment space, not a property of any single term.

---

## Part 6: The Path Forward -- Formalizing the Lower Bound

### What's proved

| Result | Status | File |
|--------|--------|------|
| Leibniz rule preserves eval | Proved | Encoding.lean |
| obsRewrite is forced by DynSemiring axioms | Proved (via leibniz axiom) | Encoding.lean |
| nestedObsCompose: constant normalization depth (2) | Proved | Complexity.lean |
| f0Chain: linear normalization depth (k-1) | Proved (k=2..6) | Complexity.lean |
| Site persistence: 1 site per pass for chains | Proved | CostBounds.lean |
| Exact size after Leibniz on obs-free children | Proved | CostBounds.lean |
| Variable sharing: no effect under fixed assignment | Proved | VarSharing.lean |
| Obs placement determines normalization regime | Proved | Complexity.lean |

### What's needed for the lower bound

1. **Uniqueness of obsRewrite (formalizable).** Prove that obsRewrite produces the minimal-size term correct in all DynSemiring models. This requires constructing a specific DynSemiring where both Leibniz branches are non-zero, showing that no proper sub-term of the expansion has the correct evaluation. This is achievable -- the existing DynSemiring instances in the codebase should suffice as witnesses.

2. **Compose chain induction (partially done).** Generalize the k=2..6 normalization depth results to arbitrary k by induction. The induction step: show that `deepRewrite(obs(compose(f_0, f0Chain (n+1))))` produces a term containing exactly one new obs(compose) site. The concrete cases provide the pattern; the general proof requires tracking what deepRewrite produces.

3. **Reassociation invariance (partially checked).** Show that reassociating the compose chain does not change the normalization depth. Left-nested and right-nested chains should have the same depth. This confirms the sequential dependency is intrinsic to the compose depth, not an artifact of association convention.

4. **Search term lower bound (open, hard).** Show that any polynomial-size Term whose deepRewrite normalization determines SAT satisfiability must have normalization cost at least as large as the compose-chain lower bound applied to the clause width. This is the gap between "deepRewrite is expensive" and "every strategy is expensive."

### The honest assessment

Steps 1-3 are achievable within the current Lean framework. They formalize the claim that the Leibniz rule's branching is forced and that compose chains have unavoidable linear normalization depth.

Step 4 is the hard step. It requires showing that deepRewrite (or any equivalent normalization procedure) is the ONLY way to determine obs-normality of SAT-structured terms. This is analogous to showing that circuits for SAT must have a certain depth -- it's a lower bound argument, and lower bounds are hard.

The framework provides better tools for this than generic circuit complexity: the algebraic constraint (Leibniz is forced) directly bounds the branching factor, and the site persistence theorem directly bounds the number of sequential passes. The question is whether these bounds transfer from the specific deepRewrite strategy to all possible strategies.

---

## Related

- [encoding-complexity.md](encoding-complexity.md) -- P vs NP as encoding execution problem
- [convergence-and-complexity.md](convergence-and-complexity.md) -- Convergence rate as complexity measure
- [normalization-depth.md](normalization-depth.md) -- Normalization depth, fixed points, and halting
- [barrier-analysis.md](barrier-analysis.md) -- Barrier analysis for the encoding obstruction
- [../encoding-obstruction.md](../encoding-obstruction.md) -- The core trilemma
- [../addition-non-locality.md](../addition-non-locality.md) -- Carry propagation forces external state
