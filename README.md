# defeater

A reasonable-reflection artifact in the **dual shape to climber**: a
system whose conclusions are *qualified* under proposer/gate control,
with each rung admitting defeaters whose soundness as exceptions is
kernel-blessed by an independent metalanguage certificate.

> **Climber checks theory construction; defeater checks
> theory qualification.**

The proposer (an LLM, in the full version) does not propose theorems
or tactics. It proposes **new sound exception schemas** — schemas
with defeasibility certificates — and the kernel admits or refuses
based on whether the certificate type-checks against the metalanguage
interp. Admitted defeaters enter the theory at the proposed rung;
conclusions at and above that rung change; the system has
*qualified*.

This is the LCF discipline applied to **proof-system qualification** —
the non-monotonic dual of climber, in which the kernel governs not
what gets added but what gets withdrawn under specific evidence.

In the keynote portfolio:

| artifact | what the gate governs |
|---|---|
| lean-grey | evaluator modification |
| lean-green | causal `set!` on a heap cell |
| LeanDisco | discovery of theorems and heuristics |
| sc-mini | program-transformation rewrites |
| climber | the right to extend the proof system itself |
| **defeater** | **the right to qualify conclusions of the proof system** |

## The structural bet

Defeasible logics always need an external order to make
non-monotonicity well-behaved: priorities, specificity, preferred
models, system Z's ε-rankings. A reflective tower already supplies
one for free. Levels become epistemic states; defeaters propagate
causally downward (Smith's connection put to non-monotonic use).
**The tower is the semantics.**

## Status

Built. The four files compile end-to-end on Lean 4.29.1 with no
`sorry` and no added axioms (`lake build`). The substrate is the
minimal version of the design space described below; richer
versions are flagged under *Open questions*.

## What lives here

- **`Defeater/Object.lean`** — the object substrate.
  - `Atom`: `String`. The substrate is ground propositional.
  - `DefRule`: a typed pair `(prems : List Atom, concl : Atom)`.
    All rules are defeasible; defeaters carry the exception logic.
  - `Env`: `Atom → Prop`. The standard interpretation.
  - `DefRule.validUnder`: a rule is valid under `env` iff
    `(∀ p ∈ prems, env p) → env concl`.
  - `Concl`: ungated forward-chaining closure of facts under rules
    (the level-0 baseline, no defeaters).
  - `Concl.sound`: every concluded atom holds under any env that
    satisfies the facts and validates the rules. The defeater layer
    weakens the second premise.

- **`Defeater/Tower.lean`** — the level-indexed defeater layer.
  - `SoundDefeater env`: target rule + trigger atom + undercutter
    list + a **defeasibility certificate** showing that under
    `env`, when the trigger holds and no undercutter holds, the
    targeted rule's conclusion fails. The certificate is what the
    kernel checks; it is parameterized by a fixed `env` because
    defeasibility is contingent (unlike climber's universally
    classically-valid axiom schemas).
  - `Tower env`: rules + rung-indexed facts + rung-indexed
    defeaters certified against `env`.
  - `Tower.factsUpTo`, `Tower.defsUpTo`: cumulative views.
  - `SoundDefeater.fires`: a defeater fires at rung `n` iff its
    trigger is among the cumulative facts at rung `n` and no
    undercutter is. Syntactic; sidesteps the negative-occurrence
    problem.
  - `Tower.isUndefeated n r`: no admitted defeater fires against
    rule `r` at rung `n`.
  - `Tower.ConclAt T n`: level-indexed derivability —
    forward chaining at rung `n` using only undefeated rules.
  - `Tower.rung_sound`: **headline metatheorem.** At every rung,
    conclusions hold under any env that satisfies the rung's
    facts and validates its undefeated rules. Proof: induction
    over the derivation.

- **`Defeater/Demo.lean`** — Tweety, end-to-end.
  - `tweetyEnv`: the standard env (rocket-strapped penguin).
  - `birdFliesRule`: `bird ⇒ flies`.
  - `penguinDefeater`: target = `birdFliesRule`, trigger =
    `penguin`, undercutters = `[rocket]`, certificate type-checks
    against `tweetyEnv`.
  - `tweetyTower`: rules = `[birdFliesRule]`; facts at rungs 0/1/2
    are `[bird]/[penguin]/[rocket]`; defeaters at rung 1 = `[penguinDefeater]`.
  - `rung0_concludes_flies`: `Tower.ConclAt tweetyTower 0 "flies"`.
  - `rung1_no_flies`: `¬ Tower.ConclAt tweetyTower 1 "flies"`.
  - `rung2_concludes_flies`: `Tower.ConclAt tweetyTower 2 "flies"`.

- **`Defeater/Counter.lean`** — non-monotonicity witnesses.
  - `flies_oscillates`: the three demo theorems packaged as a
    single witness that `flies` is concluded, then not, then again.
  - `descent_witness` / `ascent_witness`: existential statements
    of non-monotonicity in both directions.
  - `conclusions_not_monotone`: the conclusion-set function is
    not monotone in the rung index — the syntactic proof that
    defeaters are doing real semantic work.

## Headline picture

```
            ⊢_0 flies(Tweety)        ⊬_1 flies(Tweety)        ⊢_2 flies(Tweety)
            ─────────────────        ─────────────────         ─────────────────
rules:      bird ⇒ flies             bird ⇒ flies              bird ⇒ flies
                                     penguin defeats           penguin defeats
                                                               rocket undercuts penguin
```

Each rung is sound under its own epistemic state. The tower records
the audit trail: which defeater at which rung, with what defeasibility
certificate.

## Relation to climber

| | climber | defeater |
|---|---|---|
| polarity | strengthening | qualifying |
| modification | `SoundExtension` (axiom-schema + soundness cert) | `SoundDefeater` (exception-schema + defeasibility cert) |
| effect on conclusions | new theorems become derivable | old conclusions become conditional |
| headline metatheorem | `climb_sound` | `rung_sound` |
| shape | linear stages, global conclusions | level-indexed, non-monotonic in level |
| kernel discipline | proposer presents cert; kernel admits | proposer presents cert; kernel admits |

Same kernel, opposite polarity, different shape.

## Scope

Defeasible logic has a deep design space: argumentation frameworks
(Dung, ASPIC+), preference orders, preferred/grounded extensions,
floating conclusions, undercutting vs. rebutting defeaters,
specificity calculi (Reiter, Pollock, Pearl, Nute, Antoniou). This
artifact commits to *one* minimal substrate so the reflective story
stays sharp; substrate generalization is future work.

## Design choices made

These could go differently in a follow-on; flagging them so the
keynote can cite the artifact while leaving room to redesign:

- **Single-env certificates.** `SoundDefeater env` is parameterized
  by a fixed standard interpretation, not universally quantified
  over envs. Climber's `SoundExtension` is `∀ env, ...` because
  axiom schemas are classically valid in every env; defeaters
  encode contingent defaults, so the certificate holds in a
  specific semantic universe. The kernel discipline transfers; the
  certificate's universe of discourse narrows.
- **Syntactic firing.** A defeater fires when its trigger is among
  the *asserted* facts at its rung, not when its trigger is
  *derived*. This sidesteps the negative-occurrence problem in the
  inductive definition of `ConclAt` and keeps the demo concrete.
  Derived-trigger defeating is a natural extension; it would
  require stratified fixpoints rather than a clean inductive.
- **Undercutters as direct-attached.** A defeater carries its own
  list of undercutter atoms. Defeater-of-defeaters via separate
  meta-defeaters (Pollockian) is a richer alternative.

## Open questions

- **What's the equational theory at the limit?** A candidate result
  for §4.1 of the keynote: the limit reasoner's equational theory
  is exactly the strict-rule fragment, with all defeasible content
  reduced to its surviving instances.
- **`tower_stabilizes` under what conditions?** Not yet proved.
  Finite total height suffices trivially; well-founded defeat
  ordering should also suffice.
- **What does an LLM proposer look like for this artifact?** The
  kernel checks `defeats : env trigger → ... → ¬ env concl`. The
  proposer's job is to propose `(rule, trigger, undercutters,
  defeats-proof)` quadruples; the gate type-checks the proof. A
  next step is wiring this into a proposer-LLM cascade analogous
  to climber's runner.
