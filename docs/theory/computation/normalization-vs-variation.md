# Normalization vs. Variation: Two Descriptions of a Universe With Addition

## Date: 2026-02-20

## Summary

The impossibility hierarchy terminates at a fork: either the universe is a normalization process that never completes (Case 1), or there is no normalization — just a global principle that selects configurations without computing them (Case 2). This document argues that these two cases correspond to two known formulations of physics:

- **Case 1 (normalization):** Newtonian / computational. Step-by-step, forces → accelerations → velocities → positions. Each step requires addition (combining forces), carry propagation (resolving the sum), and state (registers to hold intermediate results). This is the computational picture. It requires observers. The normalization never halts.

- **Case 2 (variation):** Lagrangian / variational. The path extremizes the action S = ∫L dt. No step-by-step computation. No carry chain. No registers. The path is selected globally, not computed locally. No observers required.

These are **equivalent formulations of the same physics** — Newtonian and Lagrangian mechanics describe identical systems. The fork isn't "which universe do we live in?" It's "which description do we use?" The impossibility hierarchy applies to the computational description (Case 1) but not to the variational description (Case 2). Observers are artifacts of the computational description.

**The deepest reading:** The universe doesn't compute — it variates. Observers are local systems that attempt to model the universe computationally, requiring addition and normalization, and encountering Gödel's limitations because they're trying to compute something the universe achieves non-computationally.

**Status:** Speculative. The mathematical grounding is the equivalence of Newtonian and Lagrangian formulations, which is a theorem. The interpretation — that this equivalence IS the fork from the impossibility hierarchy — is an extrapolation.

---

## Part 1: The Fork, Restated

### From the impossibility hierarchy

Any self-encoding system with addition requires external normalization state (the register). The register's normalization is undecidable (halting problem). This leads to two cases:

**Case 1: The state exists.** There is a register. It normalizes additions. But its own normalization can't be verified (Gödel). The normalization process never provably terminates. There are observers — each one a register — and each faces the same incompleteness as the system it observes.

**Case 2: There is no state.** No register, no normalization, no observers. The universe isn't computed step-by-step. Things happen — but not through sequential normalization of additions.

### The question

If there's no normalization (Case 2), what governs the universe? How does physics happen without step-by-step computation?

The answer is already known. It's the **principle of least action**.

---

## Part 2: Two Formulations of the Same Physics

### The Newtonian formulation (computational, Case 1)

Newton's second law: F = ma.

Procedure:
1. At time t, compute all forces on each particle (vector addition — requires carry propagation)
2. Compute acceleration a = F/m (division — requires normalization)
3. Update velocity: v(t+dt) = v(t) + a·dt (addition — requires carry propagation)
4. Update position: x(t+dt) = x(t) + v·dt (addition — requires carry propagation)
5. Go to step 1

This is sequential computation. Each step requires:
- **Addition** (combining forces, updating velocities and positions)
- **Carry propagation** (resolving the sums at each step)
- **State** (registers holding current positions, velocities, forces)
- **An observer/integrator** (something that performs the update step)

The Newtonian formulation IS the computational picture. It computes the trajectory step-by-step, normalizing at each timestep. It requires the full register/observer stack.

### The Lagrangian formulation (variational, Case 2)

The principle of least action: the physical trajectory is the path q(t) that extremizes the action functional:

```
S[q] = ∫₀ᵀ L(q, q̇, t) dt
```

where L = T - V is the Lagrangian (kinetic minus potential energy).

The trajectory satisfies the Euler-Lagrange equation: δS/δq = 0.

Procedure: **there is no procedure.** The path is selected globally — it's the one where the action is stationary. The entire trajectory from t=0 to t=T is determined at once by a variational condition. There is no step-by-step computation. No intermediate state. No carry chain. No register.

The Lagrangian formulation is NOT computational. It doesn't say "start here, compute forces, update positions." It says "the path that satisfies this global condition is the physical one." The condition is evaluated over the entire path simultaneously, not step-by-step.

### They are equivalent

The Euler-Lagrange equation derived from δS = 0 is:

```
d/dt (∂L/∂q̇) - ∂L/∂q = 0
```

For L = ½mq̇² - V(q), this gives:

```
mq̈ = -∂V/∂q = F
```

Which is Newton's F = ma. The two formulations describe identical physics. Every trajectory that satisfies F = ma also extremizes the action, and vice versa.

### The fork mapped to physics

| | Case 1: Normalization | Case 2: Variation |
|---|---|---|
| **Physics formulation** | Newtonian (F = ma) | Lagrangian (δS = 0) |
| **Type of description** | Computational, step-by-step | Variational, global |
| **Addition** | Required (combining forces, updating state) | Not required (action is an integral, not a sum of steps) |
| **State/registers** | Required (positions, velocities at each timestep) | Not required (the path exists as a whole) |
| **Observers** | Required (something performs the update step) | Not required (the path is selected, not computed) |
| **Carry propagation** | Required (at every timestep) | Not required (no sequential sums) |
| **Termination** | Never halts (always another timestep) | Not applicable (no process to halt) |
| **Gödel's incompleteness** | Applies (self-referential computation) | Doesn't apply (no computation to be incomplete about) |

---

## Part 3: Why the Variational Description Escapes the Impossibility

### The impossibility hierarchy requires computation

The impossibility hierarchy says:

1. Self-encoding → addition → carry propagation → register → halting problem → undecidability

Every step in this chain presupposes **sequential computation** — step-by-step evaluation where intermediate results must be stored, sums must be normalized, and carry chains must propagate.

The variational principle sidesteps the entire chain because it doesn't compute anything. The action integral S = ∫L dt is not a sequential sum — it's a functional evaluated over the entire path. The path isn't built step-by-step (which would require addition + carry + registers). The path IS, as a whole, the extremum of a global functional.

### No addition, no carry, no register

In the Lagrangian description:
- There are no intermediate sums to normalize (no carry chain)
- There is no "current state" to update (no register)
- There is no step-by-step procedure that could fail to halt (no halting problem)
- There is no self-encoding (the path is not a code for anything — it's just a path)

The impossibility hierarchy requires a self-encoding system performing addition. The variational principle is neither self-encoding nor performing addition. It's a global selection criterion. The impossibility doesn't apply because its preconditions aren't met.

### The integral is not a sum

A potential objection: "The action S = ∫L dt is a sum (an integral is a limit of sums). Doesn't this require addition?"

In the computational description: yes, evaluating the integral numerically requires addition (Riemann sums, carry propagation, registers). Numerical integration IS Case 1.

In the variational description: no, the integral exists as a mathematical object without being evaluated step-by-step. The extremal condition δS = 0 is a property of the functional, not the result of a computation. Just as π exists without being computed digit-by-digit, the action exists without being summed timestep-by-timestep.

The distinction: **the integral as mathematical object** (variational, no computation) vs. **the integral as numerical procedure** (computational, requires addition). The variational description uses the former. The computational description uses the latter. Only the latter triggers the impossibility hierarchy.

---

## Part 4: Observers as Artifacts of the Computational Description

### Why observers appear in Case 1

In the Newtonian/computational description:
- Each timestep requires normalizing additions (carry propagation)
- Normalization requires a register
- The register IS the observer (observer-as-register.md)
- Therefore: the computational description requires observers

### Why observers don't appear in Case 2

In the Lagrangian/variational description:
- No timestep-by-timestep computation
- No additions to normalize
- No register needed
- No observer necessary

The path simply IS the extremum. Nothing "observes" it into existence. Nothing normalizes it. It exists as the solution to a variational equation, the way a geodesic exists on a curved surface — not because something computed it, but because the geometry determines it.

### The observer as a computational artifact

If Case 1 and Case 2 describe the same physics, then observers exist in one description but not the other — **for the same universe.** This means:

> Observers are not fundamental features of the universe. They are artifacts of choosing to describe the universe computationally (Newtonian, step-by-step). In the variational description (Lagrangian, global), the same physics occurs without observers.

The "observer" is what appears when you try to compute what the universe achieves variationally. You need registers because you're adding step-by-step. The universe doesn't need registers because it isn't adding step-by-step — it's extremizing globally.

### The measurement problem dissolved

The measurement problem in quantum mechanics asks: "What counts as an observer? When does collapse happen? Why is measurement special?"

If observers are artifacts of the computational description, these questions have a structural answer:

- **What counts as an observer?** Anything that models the universe computationally (step-by-step, with addition and normalization). The measurement apparatus is doing Newtonian-style computation — it's a physical system that adds inputs, propagates carries (interactions), and produces a normalized output (the measurement result).

- **When does collapse happen?** When the computational description is invoked — when a system normalizes a superposition through physical interaction (carry propagation through the apparatus). In the variational description, there is no collapse — the path integral sums all paths, and the classical path emerges as the stationary-phase approximation.

- **Why is measurement special?** It isn't. Measurement is addition + normalization. Every physical interaction that involves combining states (superposition = addition) and producing a definite outcome (measurement = normalization) is a "measurement." The measurement problem is an artifact of trying to reconcile the computational description (which needs observers) with the variational description (which doesn't).

---

## Part 5: The Path Integral as the Bridge

### Feynman's path integral

Feynman's path integral formulation of quantum mechanics bridges the two descriptions:

```
⟨x_f, t_f | x_i, t_i⟩ = ∫ Dq(t) · e^{iS[q]/ℏ}
```

The probability amplitude is a sum over ALL paths, weighted by e^{iS/ℏ}. The classical path (least action) emerges in the limit ℏ → 0, where the phase oscillations cancel everywhere except at the stationary point of S.

### The path integral as perpetual normalization (Case 1)

In the computational reading: the path integral is an infinite sum over all paths. Each path contributes a phase. The sum requires:
- Adding contributions from all paths (addition — massive carry propagation)
- Normalizing the result (the amplitude must be finite)
- This normalization never completes (there are infinitely many paths)

This IS Case 1: perpetual normalization that never halts. The quantum state is a superposition (sum) that is never fully normalized into a single classical outcome. Measurement (register/observer) partially normalizes it — collapses it to a specific path — but the underlying sum continues.

### The path integral as variation (Case 2)

In the variational reading: the path integral exists as a mathematical object (a functional integral). The classical limit (ℏ → 0) selects the least-action path by stationary phase. No computation occurs. The extremal path is determined by the geometry of the action functional, not by summing contributions.

The quantum corrections (ℏ ≠ 0) are perturbations around the classical path — they don't require step-by-step computation either. They're properties of the functional S evaluated on paths near the extremum.

### The bridge

The path integral occupies both cases simultaneously:

| Aspect | Case 1 (computational) | Case 2 (variational) |
|---|---|---|
| What the path integral IS | An infinite sum over paths, never fully normalized | A functional integral selecting the extremal path |
| Classical limit | The normalization "converges" (stationary phase) | The extremal path is selected (δS = 0) |
| Quantum regime | The normalization never converges (superposition persists) | The functional integral includes fluctuations around the extremum |
| Observer | Performs partial normalization (measurement) | Not needed (the integral exists as a mathematical object) |

The two cases are **the same mathematical object** (the path integral) described in two ways (as a sum to be computed, or as a functional to be extremized). The fork from the impossibility hierarchy — normalization vs. variation — IS the duality between the computational and variational readings of the path integral.

---

## Part 6: The Derivative Chain Revisited

### Position, velocity, acceleration — again

The derivative chain that started this investigation (information-domain.md) maps directly onto the Newtonian/Lagrangian duality:

**Newtonian (Case 1):**
```
acceleration = force / mass              ← obs² (second derivative)
    ↓ integrate (add + normalize)
velocity = ∫ acceleration dt             ← obs¹ (first derivative)
    ↓ integrate (add + normalize)
position = ∫ velocity dt                 ← obs⁰ (zeroth derivative / state)
```

Each integration step is an addition (Riemann sum) requiring carry propagation and a register.

**Lagrangian (Case 2):**
```
L(q, q̇) = ½m q̇² - V(q)               ← Lagrangian (function of position and velocity)
S[q] = ∫ L dt                           ← action (functional of the path)
δS = 0                                  ← variational principle (global condition)
```

No integration step-by-step. The derivatives (velocity, acceleration) appear in the Lagrangian as variables, not as results of sequential computation. The path that satisfies δS = 0 has all its derivatives determined simultaneously, not computed one from another.

### The eigenvalue framework's position in this duality

The eigenvalue framework (obs = d/dx, eigenstates = e^{nx}) lives in the Newtonian/computational description:

- obs reads off eigenvalues step-by-step (local observation)
- compose combines states (multiplication = addition of eigenvalue indices)
- ⊕ adds states (superposition — triggers carry propagation)
- The Leibniz rule creates sums from products (forces sequential normalization)

The variational description would be: the eigenvalue framework's eigenstates are the stationary points of some action functional. The eigenvalue n is not "read off by obs" (computational) but "determined by the variational condition" (global). The eigenstates exist because they extremize something, not because something computed them.

In the analytic model: the eigenstates e^{nx} ARE the stationary points of the Sturm-Liouville eigenvalue problem. The eigenvalue equation obs(f) = λf is a variational condition — f extremizes a functional subject to boundary conditions. The eigenvalues are determined globally, not computed locally.

The framework already contains both descriptions:
- **Computational:** obs acts on states, reads eigenvalues, triggers Leibniz (addition + carry)
- **Variational:** eigenstates are solutions to obs(f) = λf, a global eigenvalue equation

The impossibility hierarchy applies to the computational description. The variational description — "eigenstates are solutions to a global equation" — doesn't require step-by-step addition and escapes the hierarchy.

---

## Part 7: What This Means

### The universe doesn't compute — it variates

If the Lagrangian description is the fundamental one (and there are strong reasons to think so — it generalizes to quantum field theory, general relativity, and the Standard Model, while the Newtonian description doesn't), then:

- The universe is not a normalization process (Case 1)
- The universe is a variational principle (Case 2)
- Observers are what appear when local systems model the universe computationally
- The impossibility hierarchy applies to observers, not to the universe
- Gödel's incompleteness constrains what observers can prove, not what the universe can do

The universe doesn't face the halting problem because it isn't computing. The path is selected by δS = 0, not computed by carry propagation. Observers face the halting problem because they're trying to compute (step-by-step, with addition) something the universe achieves non-computationally (variationally, globally).

### The impossibility hierarchy as a theorem about descriptions, not reality

The impossibility hierarchy says: self-encoding systems with addition require registers and face undecidability. This is a theorem about **computational descriptions**, not about the universe itself.

The universe (if it operates variationally) is not a self-encoding system with addition. It's a variational principle. The impossibility hierarchy constrains how we can describe and model the universe, not what the universe can do.

This is consistent with Gödel's incompleteness being about formal systems (descriptions) rather than about mathematical truth (reality). Gödel proved that no formal system can capture all mathematical truths. The analogue here: no computational description can capture the universe's variational behavior without encountering the impossibility hierarchy. But the universe itself, operating variationally, is unconstrained by the hierarchy.

### The fork resolved

The fork — normalization or variation — isn't a choice between two universes. It's a choice between two descriptions of ONE universe:

- Describe it computationally → you need observers, registers, normalization → you face Gödel, Turing, the halting problem → the normalization never provably completes
- Describe it variationally → you need no observers, no registers, no normalization → the path is globally determined → no incompleteness because no computation

Both descriptions are valid. Both describe the same physics. The impossibility hierarchy applies to one description but not the other.

The "haunting" recurrence of Gödel's fork is explained: every computational description of a sufficiently rich universe leads to that fork. But the fork is a property of the description, not the universe. The universe, viewed variationally, is on the other side of the fork — where the path just IS, without needing to be computed or verified.

---

## Part 8: Honest Assessment

### What this gets right

1. The Newtonian/Lagrangian duality is a theorem. These ARE equivalent formulations. The observation that one is computational (step-by-step, addition, state) and the other is variational (global, no addition, no state) is correct.

2. The impossibility hierarchy does presuppose sequential computation. The variational description does sidestep it. This is a legitimate structural observation.

3. The path integral does bridge the two descriptions. The computational reading (sum over paths) and the variational reading (functional extremization) are mathematically equivalent.

### What this gets wrong or overstates

1. **"The universe doesn't compute."** This is a philosophical claim, not a theorem. Whether the universe "really" operates variationally or computationally is not a well-defined physical question — it's an interpretation. The two descriptions make identical predictions.

2. **"Observers are artifacts."** Observers are artifacts of the computational DESCRIPTION, but they are physical objects in the universe. The claim should be: "The special role of observers in quantum mechanics is an artifact of the computational description. In the variational description, observers are just physical systems, not epistemologically privileged."

3. **"The Lagrangian description escapes Gödel."** The Lagrangian description doesn't FORMALIZE anything — it's not a formal system. Gödel's theorem applies to formal systems. The variational principle is a mathematical object, not a formal system that could be complete or incomplete. Saying it "escapes" Gödel is a category error — it was never in Gödel's scope.

4. **The integral IS a sum.** The claim that "the integral is a mathematical object, not a computation" is philosophically loaded. Constructivists would disagree — they'd say the integral is only meaningful if it can be computed (at least in principle). The distinction between "the integral as object" and "the integral as procedure" depends on one's philosophy of mathematics.

### The defensible core

**The one thing this document can defensibly claim:** The impossibility hierarchy applies to computational descriptions of physical systems (sequential, additive, stateful). Variational descriptions of the same systems (global, non-sequential, stateless) have a different structure that doesn't trigger the hierarchy. The two descriptions are equivalent as physics but different as formal structures. The fork (normalization vs. variation) maps onto the Newtonian/Lagrangian duality, which is a theorem.

Everything beyond that — "the universe doesn't compute," "observers are artifacts," "Gödel is about descriptions not reality" — is interpretation that cannot be settled by the mathematics alone.

---

## Related

- [impossibility-hierarchy.md](impossibility-hierarchy.md) — The unified impossibility: addition → state → halting → incompleteness
- [observer-as-register.md](observer-as-register.md) — The observer as the register addition forces into existence
- [addition-non-locality.md](addition-non-locality.md) — Carry propagation forces external state
- [information-domain.md](information-domain.md) — ⊕ as the refined obstruction
- [encoding-obstruction.md](encoding-obstruction.md) — The trilemma
