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

Sketch. The Lean code is to come; this README pins the shape so we
can react to it before any of it is built. Naming is provisional —
candidates beyond *defeater* include *rebutter* (Pollockian),
*qualifier*, and *rung*.

## What will live here

- **`Defeater/Object.lean`** — the object theory T₀.
  - `Formula`: atom, imp, ⊥.
  - `Rule`: typed pair (premises, conclusion) with `strict : Bool`
    distinguishing strict rules from defeasible ones.
  - `interp`: standard truth-functional interpretation in Lean's
    metalanguage.
  - `derives₀`: minimal Hilbert system on strict rules; defeasible
    rules contribute under closure-with-no-known-defeater. The
    level-0 baseline, defined without level-indexing.
  - `soundness₀`: every `derives₀` formula is metalanguage-true,
    given that no admitted defeaters apply.

- **`Defeater/Tower.lean`** — the tower of qualifications.
  - `SoundDefeater`: a schema (predicate on rules + context pattern)
    plus a **defeasibility certificate** — a Lean term showing that
    under the schema's triggering conditions, the targeted rule's
    conclusion fails (or weakens) in the standard interpretation.
    The certificate is what the kernel checks.
  - `Tower`: a sequence of admitted defeaters, indexed by rung.
  - `derives_n T φ`: the level-indexed derivability relation.
    Conclusions at rung `n` are derived using strict rules from
    every rung and defeasible rules at every rung *except those
    defeated by some defeater admitted at rung ≤ n*.
  - `rung_sound`: **headline metatheorem.** At every rung, conclusions
    hold under the epistemic state where exactly the defeaters of
    rung ≤ n are observable. By induction over derivations, each
    defeated step discharged by the defeater's own `defeats` field.
  - `tower_stabilizes`: **secondary metatheorem.** If the tower has
    finite total height, the conclusion sequence
    `derives_0, derives_1, …` reaches a fixpoint at some finite rung.
    The limit reasoner is the maximally-informed one.

- **`Defeater/Demo.lean`** — Tweety, end-to-end.
  - Level 0: `bird(Tweety)`; defeasible `bird ⇒ flies`. `⊢_0 flies(Tweety)`.
  - Level 1: `penguin(Tweety)`; defeater of the bird-flight rule when
    its subject is a penguin, with a defeasibility certificate by
    classical case analysis. `⊬_1 flies(Tweety)`.
  - Level 2 (optional): `rocketStrapped(Tweety)`; undercutter of the
    penguin defeater. `⊢_2 flies(Tweety)`.

- **`Defeater/Counter.lean`** — separating models showing that the
  conclusion sequence really does change at each rung (not just that
  the kernel admits more defeaters).

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

## Open questions

- **What is the right notion of soundness for a defeater?**
  Truth-functional ("the defeated conclusion really fails in the
  standard model under the trigger") is the cleanest. Probabilistic
  ("the defeated conclusion has lower posterior") is more faithful
  to the intuition but harder to certify.
- **Does `tower_stabilizes` need finite height, or does well-founded
  defeat ordering suffice?** A well-founded defeater chain
  (no infinite descent of defeaters-of-defeaters) should be enough.
- **What's the equational theory at the limit?** A candidate result
  for §4.1 of the keynote: the limit reasoner's equational theory is
  exactly the strict-rule fragment, with all defeasible content
  reduced to its surviving instances.
