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
  - `Tower.ConclAt_succ_of_empty`: one-step stabilization — if no
    new facts or defeaters are admitted at rung n+1, conclusions
    at rung n+1 coincide with conclusions at rung n.
  - `Tower.tower_stabilizes`: **secondary metatheorem.** If the
    tower admits no facts or defeaters past rung K, the conclusion
    sequence is constant from K onward. Proof: induction on n
    using the one-step stabilization. The "limit reasoner" of the
    keynote framing is the rung-K reasoner.

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
  - `tweety_rung2_sound`: `rung_sound` applied to the demo —
    every conclusion at rung 2 holds under `tweetyEnv`. The
    metatheorem instantiated end-to-end.

- **`Defeater/Counter.lean`** — non-monotonicity and stability.
  - `flies_oscillates`: the three demo theorems packaged as a
    single witness that `flies` is concluded, then not, then again.
  - `descent_witness` / `ascent_witness`: existential statements
    of non-monotonicity in both directions.
  - `conclusions_not_monotone`: the conclusion-set function is
    not monotone in the rung index — the syntactic proof that
    defeaters are doing real semantic work.
  - `tweetyTower_stabilizes`: a corollary of `tower_stabilizes`
    instantiated for the Tweety tower — conclusions are constant
    from rung 2 onward.

- **`Defeater/Reflection.lean`** — reflective defeater semantics.
  - `Closure rules active facts`: ungated forward-chaining gated
    by an `active` predicate. The shared inductive scaffolding for
    both syntactic and reflective semantics.
  - `Closure.sound`: every closed atom holds under any env that
    satisfies the facts and validates active rules.
  - `Tower.ReflConclAt T n`: *reflective* derivability — defined by
    structural recursion on `n` so the body for `n+1` references
    only `ReflConclAt T n` (sidesteps negative-occurrence). At rung 0
    no defeaters fire (no prior stage); at rung n+1 a defeater fires
    when its trigger was *concluded* at rung n.
  - `Tower.isUndefeatedRefl`: standalone form of the reflective
    undefeated predicate.
  - `Tower.reflConclAt_eq`: `ReflConclAt T n = Closure under isUndefeatedRefl`.
  - `Tower.refl_rung_sound`: **reflective per-rung soundness** —
    same shape as `rung_sound`, with reflective firing.

- **`Defeater/ReflDemo.lean`** — reflective Tweety, end-to-end.
  - Two rules: `bird ⇒ flies`, `penguin ⇒ cantFly`.
  - `cantFlyDefeater`: targets `bird ⇒ flies`, trigger `cantFly`.
    The trigger is *derived* (not asserted) — it appears in the
    rung-0 conclusion set via `penguin ⇒ cantFly`.
  - `rung0_concludes_flies` / `rung0_concludes_cantFly`: rung 0
    is the unconstrained baseline; both rules fire.
  - `rung1_no_flies`: at rung 1 the defeater fires *reflectively*
    on the rung-0 inference of `cantFly`; `bird ⇒ flies` is
    defeated; `flies` is not concluded.
  - `rung1_concludes_cantFly`: defeating one rule doesn't disturb
    others; `penguin ⇒ cantFly` stays active.

  This is the keynote thesis instantiated literally: the upper rung
  observes the lower rung's *inferences* and intervenes. The
  syntactic version of Tweety can't tell this story — its defeater
  fires on a primitive assertion; here the trigger is a derivation.

- **`Defeater/Nixon.lean`** — the Nixon Diamond (the textbook
  example of *symmetric* defeasible conflict since Reiter).
  - Two rules: `Quaker ⇒ pacifist`, `Republican ⇒ nonpacifist`.
  - Two defeaters: each rule's conclusion is the other defeater's
    trigger.
  - `nixon_credulous_at_rung0`: at rung 0 (before reflective
    defeating), both conclusions hold — the credulous reading.
  - `nixon_skeptical_at_rung1`: at rung 1, both rules are defeated
    reflectively, neither conclusion holds — the skeptical reading.
  - `nixon_diamond_irresolution`: the framework refuses to choose;
    the credulous and skeptical readings live at adjacent rungs and
    the conclusion sequence oscillates.

  Same structural shape as `Oscillate.lean`, but with the textbook
  semantic gloss: the canonical case where defeasible logic has no
  preferred answer is exactly the case where reflective firing
  oscillates.

- **`Defeater/Oscillate.lean`** — reflective non-stabilization
  counterexample.
  - Rules: `z ⇒ x` and `x ⇒ y`. A defeater of `x ⇒ y` triggered by
    `y` (the rule's own conclusion). All admissions at rung 0.
  - `rung0_concludes_y`: baseline closure derives `y`.
  - `rung1_no_y`: defeater fires reflectively on the rung-0
    inference of `y`; `x ⇒ y` is defeated.
  - `rung2_concludes_y`: defeater doesn't fire (since `y ∉ ReflConclAt 1`);
    `x ⇒ y` is undefeated again; `y` is re-derived.
  - `reflective_oscillation`: the period-2 witness.

  No new admissions happen past rung 0 — yet the conclusion sequence
  oscillates forever. The syntactic stabilization theorem
  (`Tower.tower_stabilizes`) does *not* lift unconditionally to the
  reflective layer. The active predicate's dependence on prior-rung
  conclusions creates feedback loops that syntactic firing cannot
  produce. This is the structural distinction the keynote's
  reflection thesis predicts.

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
- **Two firing semantics.** Two flavors of defeater firing coexist:
  - *Syntactic* (`Tower.ConclAt`, `Tower.fires`): a defeater fires
    when its trigger is among the *asserted* facts at its rung. A
    clean inductive, but degenerate — defeasible logic in name only.
  - *Reflective* (`Tower.ReflConclAt`): a defeater fires when its
    trigger was *concluded* at the prior rung (Pollock-style,
    canonical defeasible logic). Stratified by rung to sidestep the
    negative-occurrence problem in the inductive definition.

  Both semantics share `Closure` and the per-rung-soundness shape;
  the difference is what the firing predicate observes. The keynote
  pitch — "an upper rung reasoning about a lower rung's inferences"
  — is realized by the reflective semantics.
- **Undercutters as direct-attached.** A defeater carries its own
  list of undercutter atoms. Defeater-of-defeaters via separate
  meta-defeaters (Pollockian) is a richer alternative.

## Open questions

- **What's the equational theory at the limit?** A candidate result
  for §4.1 of the keynote: the limit reasoner's equational theory
  is exactly the strict-rule fragment, with all defeasible content
  reduced to its surviving instances.
- **When does the reflective sequence stabilize?** The syntactic
  `tower_stabilizes` lifts unconditionally; the reflective version
  doesn't (see `Oscillate.lean`). A natural conditional theorem:
  *if no rule's conclusion is a defeater trigger, the reflective
  sequence stabilizes once admissions cease.* The general case —
  characterizing exactly when reflection terminates — is the
  defeasible-logic analog of Beklemishev's ordinal analysis.
- **What does an LLM proposer look like for this artifact?** The
  kernel checks `defeats : env trigger → ... → ¬ env concl`. The
  proposer's job is to propose `(rule, trigger, undercutters,
  defeats-proof)` quadruples; the gate type-checks the proof. A
  next step is wiring this into a proposer-LLM cascade analogous
  to climber's runner.
