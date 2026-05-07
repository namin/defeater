/-
  Defeater/Object.lean — the object substrate.

  Atoms, defeasible rules, environments, and validity-of-a-rule-under-an-
  environment. The substrate has no implication-as-formula; defeasibility
  itself supplies the non-monotonicity.

  At level 0 (this file) every rule is treated as "ungated default" —
  conclusions follow from premises whenever the rule is valid under env.
  Soundness is conditional: if env validates each rule and all initial
  facts hold under env, then every concluded atom holds under env.

  The level-indexed defeater layer lives in `Tower.lean`.
-/

namespace Defeater

/-- Ground propositional atom. -/
abbrev Atom := String

/-- A defeasible rule: a list of premise atoms and a single conclusion
    atom. The substrate is ground; rule schemas with variables are
    expressed by enumerating instances. -/
structure DefRule where
  prems : List Atom
  concl : Atom
  deriving Repr, DecidableEq

/-- An environment maps atoms to metalanguage propositions. The
    "standard interpretation" of the object substrate. -/
abbrev Env := Atom → Prop

/-- A rule is *valid under env* when env makes the inference go
    through: if all premises hold under env, so does the conclusion.
    A defeasible rule may *fail* validUnder for some env — that's
    exactly the case a defeater is meant to catch. -/
def DefRule.validUnder (r : DefRule) (env : Env) : Prop :=
  (∀ p ∈ r.prems, env p) → env r.concl

/-- Forward-chaining closure of `facts` under `rules`, with no
    defeaters. This is the level-0 baseline: every rule applies. -/
inductive Concl (rules : List DefRule) (facts : List Atom) : Atom → Prop where
  | fact {a : Atom} : a ∈ facts → Concl rules facts a
  | rule (r : DefRule) :
      r ∈ rules →
      (∀ p ∈ r.prems, Concl rules facts p) →
      Concl rules facts r.concl

/-- Soundness of the ungated forward chaining: every concluded atom
    holds under any env that satisfies all the facts and validates all
    the rules. The defeater layer in `Tower.lean` weakens the second
    premise (validUnder need only hold modulo defeaters). -/
theorem Concl.sound {rules : List DefRule} {facts : List Atom} {env : Env}
    (hfacts : ∀ a ∈ facts, env a)
    (hrules : ∀ r ∈ rules, r.validUnder env)
    {a : Atom} (hc : Concl rules facts a) : env a := by
  induction hc with
  | fact h => exact hfacts _ h
  | rule r hr _ ih =>
    exact hrules r hr (fun p hp => ih p hp)

end Defeater
