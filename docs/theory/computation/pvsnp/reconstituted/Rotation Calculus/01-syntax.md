# Syntax

## Terms

The language has three term constructors:

```
t ::= ground                    -- the irreducible element
    | pair(t, t)                -- composition of two terms
    | observe(t)                -- marks a term for observation
```

That's it. Three constructors. No variables, no binders, no abstraction, no application. The language is first-order.

### Ground

`ground` is the terminal symbol. It has no internal structure. It is the fixed point of observation:

```
observe(ground) = ground
```

Ground is what remains when there is nothing left to inspect. It is the base case, the atom, the fully extensional. In the spectral arithmetic framework, this is `f_1 = obs(f_1)`.

### Pair

`pair(a, b)` is the only way to build structure. It places two terms in relation. The left position is the **active** element — the one that will be observed next. The right position is the **rest** — carried content that persists through the observation.

Nesting is storage:

```
pair(a, pair(b, pair(c, ground)))
```

This is a structure containing three elements `a`, `b`, `c` arranged in a specific order. The nesting depth is the amount of stored content. No separate memory, no tape, no heap. The term IS the store.

This is a cons list. `pair` is cons. `ground` is nil. The choice is deliberate — the simplest possible recursive data structure.

### Observe

`observe(t)` marks `t` for inspection. It is not an operator that "does something to" `t` from outside. It is a structural marker that says: this subterm is next to pass through the door.

`observe` is not a function in the metalanguage. It is syntax. The rewrite rule defines what happens when `observe` meets `pair`. The meaning of `observe` is entirely determined by the rule — it has no independent semantics.

## Nesting as the Universal Store

All state is encoded in nesting:

```
-- A single element
pair(a, ground)

-- Three elements in order a, b, c
pair(a, pair(b, pair(c, ground)))

-- A tree: left branch (a, b), right branch (c, d)
pair(pair(a, b), pair(pair(c, d), ground))
```

There is no distinction between "data" and "program." A term is a term. Whether an element is "an instruction" or "a datum" depends entirely on whether it's in the active position (left of the outermost pair) or the rest position (right). And the rule rotates elements between these positions.

### Size

The **size** of a term is the number of `pair` constructors it contains. This is well-defined, finite, and strictly decreases under certain conditions (see the rewrite rule document).

### Depth

The **depth** of a term is the maximum nesting level. `ground` has depth 0. `pair(a, b)` has depth `1 + max(depth(a), depth(b))`.

For flat lists, size and depth coincide:

```
pair(a, pair(b, pair(c, ground)))    -- size 3, depth 3
```

For trees, depth can be less than size:

```
pair(pair(a, b), pair(c, ground))    -- size 3, depth 2
```

This distinction matters for complexity — it determines how many rotation steps are needed to bring every element through the observation point.

## Well-formed terms

A term is **well-formed** if:
1. Every leaf is `ground`
2. `observe` appears at most once, and only at the outermost level

Condition 2 ensures there is exactly one observation happening at a time. This is not a limitation — it's the architectural choice that head-tape unification requires. There's one observation point. Content rotates through it.

A term ready for computation has the form:

```
observe(pair(a, pair(b, pair(c, ... pair(z, ground) ...))))
```

One `observe` wrapping a nested structure. The computation is: rotate each element through the observation point until ground is reached or a constraint fails.

## Notation conventions

For readability, flat lists can be written:

```
[a, b, c]  =  pair(a, pair(b, pair(c, ground)))
```

And an observation of a list:

```
observe[a, b, c]  =  observe(pair(a, pair(b, pair(c, ground))))
```

These are purely notational — the underlying terms are as defined above.
