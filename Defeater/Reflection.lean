import Defeater.Tower

/-
  Defeater/Reflection.lean — reflective defeater semantics.

  In the syntactic semantics (`Tower.ConclAt`), a defeater fires when
  its trigger is among the asserted facts at its rung. That treats
  the lower rung as raw data — the defeater observes what was *told*,
  not what was *inferred*.

  In the *reflective* semantics defined here, a defeater fires when
  its trigger was *concluded* at the previous rung — the lower rung
  is treated as a reasoner whose inferences are themselves observable.
  This is the keynote's reflection: an upper rung reasoning about a
  lower rung's reasoning, not just its inputs. It is also closer to
  canonical defeasible logic (Pollock's OSCAR, Reiter's default
  logic, Antoniou's defeasible logic), all of which fire defeaters
  on derived beliefs.

  The negative-occurrence problem is sidestepped by *stratification*:
  `ReflConclAt T (n+1)` references `ReflConclAt T n` only — never
  itself. Lean accepts this as structural recursion on the rung index.

  At rung 0 no defeaters fire (there is no prior stage to observe);
  this is the baseline closure of all rules.
-/

namespace Defeater

/-- Closure of a list of facts under a list of rules, gated by an
    `active` predicate that selects which rules apply. The same
    inductive serves both the syntactic-firing semantics (parameter:
    isUndefeated based on facts) and the reflective semantics
    (parameter: isUndefeated based on prior conclusions). -/
inductive Closure (rules : List DefRule) (active : DefRule → Prop)
    (facts : List Atom) : Atom → Prop where
  | fact {a : Atom} : a ∈ facts → Closure rules active facts a
  | rule (r : DefRule) :
      r ∈ rules →
      active r →
      (∀ p ∈ r.prems, Closure rules active facts p) →
      Closure rules active facts r.concl

/-- Soundness of `Closure`: if env satisfies all facts and validates
    every active rule, then every closed atom holds in env. -/
theorem Closure.sound {rules : List DefRule} {active : DefRule → Prop}
    {facts : List Atom} {env : Env}
    (hfacts : ∀ a ∈ facts, env a)
    (hrules : ∀ r ∈ rules, active r → r.validUnder env)
    {a : Atom} (hc : Closure rules active facts a) : env a := by
  induction hc with
  | fact h => exact hfacts _ h
  | rule r hr hact _ ih =>
    exact hrules r hr hact (fun p hp => ih p hp)

namespace Tower

variable {env : Env}

/-- *Reflective* derivability at rung n: closure of facts up through
    rung n under rules that no admitted defeater (rung ≤ n) defeats
    *based on what was concluded at rung n-1*. Defined by structural
    recursion on n; the body for `n+1` references only `ReflConclAt T n`,
    not itself. -/
def ReflConclAt (T : Tower env) : Nat → Atom → Prop
  | 0 => fun a => Closure T.rules (fun _ => True) (T.factsUpTo 0) a
  | n + 1 => fun a =>
      Closure T.rules
        (fun r => ∀ d ∈ T.defsUpTo (n + 1),
                    d.rule = r →
                    ¬ (ReflConclAt T n d.trigger ∧
                       ∀ u ∈ d.undercutters, ¬ ReflConclAt T n u))
        (T.factsUpTo (n + 1)) a

/-- A rule is *reflectively undefeated* at rung n iff no admitted
    defeater fires reflectively. At rung 0 no defeaters can fire
    (there is no prior stage to observe), so all rules are
    undefeated. -/
def isUndefeatedRefl (T : Tower env) : Nat → DefRule → Prop
  | 0, _ => True
  | n + 1, r =>
      ∀ d ∈ T.defsUpTo (n + 1),
        d.rule = r →
        ¬ (ReflConclAt T n d.trigger ∧
           ∀ u ∈ d.undercutters, ¬ ReflConclAt T n u)

/-- The two definitions agree: `ReflConclAt T n` is exactly the
    closure under `isUndefeatedRefl T n`. By cases on n; both sides
    are definitionally equal. -/
theorem reflConclAt_eq (T : Tower env) (n : Nat) (a : Atom) :
    ReflConclAt T n a ↔
    Closure T.rules (T.isUndefeatedRefl n) (T.factsUpTo n) a := by
  cases n with
  | zero => exact Iff.rfl
  | succ _ => exact Iff.rfl

/-- **Reflective per-rung soundness.** At every rung, conclusions
    hold under any env that satisfies the rung's facts and validates
    each rule that's reflectively undefeated. Same shape as
    `rung_sound`; uses `Closure.sound` after unfolding via
    `reflConclAt_eq`. -/
theorem refl_rung_sound {T : Tower env} {n : Nat}
    (hfacts : ∀ a ∈ T.factsUpTo n, env a)
    (hrules : ∀ r ∈ T.rules, T.isUndefeatedRefl n r → r.validUnder env)
    {a : Atom} (hc : ReflConclAt T n a) : env a := by
  rw [reflConclAt_eq] at hc
  exact Closure.sound hfacts hrules hc

end Tower

end Defeater
