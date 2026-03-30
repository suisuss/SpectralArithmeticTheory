# The Rewrite Rule

## The Rule

There is one rewrite rule:

```
observe(pair(a, b)) -> pair(b, observe(a))      [R]
```

With the ground case:

```
observe(ground) -> ground                        [G]
```

That's the entire operational semantics. Two cases of a single rule.

## What the rule does

### Match

The rule fires when `observe` sits on top of a `pair`. This is the only redex — the only pattern that triggers computation. If `observe` sits on `ground`, computation halts (successfully). If `observe` sits on nothing (ill-formed), nothing happens.

### Transform

The active element `a` stays under `observe` — it's next to be inspected. The rest `b` moves to the outside — it becomes carried content.

### Carry

The internal structure of both `a` and `b` passes through unchanged. The rule doesn't look inside `a` or `b`. It only sees the outermost `pair` constructor.

### Expose

After the rewrite, `a` is under `observe`. If `a` is itself a `pair`, the rule can fire again. If `a` is `ground`, the observation terminates. The rewrite exposes whatever `a` contains for future observation.

## Execution trace

Starting from `observe[a, b, c]`:

```
   observe(pair(a, pair(b, pair(c, ground))))
-> pair(pair(b, pair(c, ground)), observe(a))         -- a is observed, rest carried
```

If `a` is ground:

```
-> pair(pair(b, pair(c, ground)), ground)              -- done, a was trivial
```

If `a` is `pair(x, y)`:

```
-> pair(pair(b, pair(c, ground)), observe(pair(x, y)))
-> pair(pair(b, pair(c, ground)), pair(y, observe(x)))
```

The observation walks into `a`, unpacking its structure while carrying everything else.

## Properties

### Termination

**Claim:** For any well-formed term `t`, repeated application of `[R]` and `[G]` terminates.

**Proof sketch:** Define `mu(t)` = the number of `pair` constructors under `observe`. Each application of `[R]` moves one `pair` constructor from under `observe` to outside `observe` (the `b` component moves out). So `mu` strictly decreases. Since `mu` is a natural number, the process terminates. When `mu = 0`, we have `observe(ground)`, which reduces by `[G]`.

This is termination by construction. No analysis needed. The rule cannot diverge because it monotonically drains the content from under `observe`.

### No symbol creation

The rule produces no new `pair`, `observe`, or `ground` symbols. It rearranges existing ones. The total number of constructors is invariant. This is a conservation law — the rule is a rearrangement, not a generation.

Compare with Leibniz: `obs(compose(a, b)) -> compose(obs(a), b) + compose(a, obs(b))` creates new symbols (`+`, two new `compose`, two new `obs`). That's where exponential blowup comes from. The rotation rule avoids this entirely.

### Confluence

**Claim:** The rule is confluent (trivially).

**Proof:** The rule has exactly one redex in any well-formed term — the `observe` sitting on the outermost `pair`. There are never two places where the rule could fire. There is no choice. Hence no divergence, hence confluence.

This is a strong property. It means the language is deterministic. Given a term, the computation is fully determined. There is exactly one normal form, reached by exactly one path.

### Reversibility

The rule is locally invertible:

```
pair(b, observe(a)) -> observe(pair(a, b))       [R-inverse]
```

Given the output, you can reconstruct the input. No information is lost in a single step. The rotation is a bijection on term structure.

This is significant: the rule preserves all information. The "information loss" discussed in the coupling document doesn't come from the rule — it comes from the constraint (see next document), which is the only place where a binary decision (accept/reject) is made.

## Observation as rewriting

The rule makes precise what "observation" means computationally:

1. **Observation is pattern-matching.** The rule checks: is the term `observe(pair(_, _))`? That check IS the observation. It doesn't happen before the rule fires — it is the rule firing.

2. **Observation is structural transformation.** The term changes. The syntax is different before and after. The transformation is the observation. There is no "result" separate from the transformed term — the result IS the transformed term.

3. **Observation is pure.** No side effects, no external state, no oracle. The rule is a function from terms to terms. Deterministic. Total. The output depends only on the input.

4. **Observation is local.** The rule sees only the outermost constructor under `observe`. It doesn't examine `a` or `b`. It doesn't need to. The local structure determines the local transformation. Global behavior emerges from iterated local observation.

## The door metaphor, formalized

Before the rule fires: `observe(pair(a, b))`. The structure is in its intensional form. `a` and `b` are composed but not yet differentiated — they sit together inside the `observe` boundary, undiscriminated.

After the rule fires: `pair(b, observe(a))`. The structure has been partially extensionalized. `b` has been separated out — it's now carried content, visible, differentiated. `a` remains under `observe` — it's next through the door.

The door is the rule. Passing through it is one step of making the implicit explicit. Normal form is when everything implicit has been made explicit — when `observe` sits on `ground` and there's nothing left to see.

## Normal forms

A term is in **normal form** when it contains no redex — no `observe(pair(_, _))` subterm.

For well-formed terms, normal forms have the shape:

```
pair(r_1, pair(r_2, ... pair(r_n, ground) ...))
```

Where each `r_i` is itself in normal form. The `observe` is gone — it has been consumed by reaching `ground`. What remains is the fully unfolded structure with all elements repositioned by the rotation.

The normal form is the result. The sequence of rewrite steps is the computation. The term before normalization is the problem.
