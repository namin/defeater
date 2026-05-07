import Defeater.Object

/-
  Defeater/Tower.lean — the level-indexed defeater layer.

  The Tower lives over a fixed standard interpretation `env : Env`.
  Defeasibility certificates are propositions about this env: when
  the trigger holds and no undercutter holds, the targeted rule's
  conclusion fails. The kernel admits a defeater iff its certificate
  type-checks against `env`.

  This is *narrower* than climber's universally-quantified soundness
  certificate (∀ env, schema φ → interp env φ): climber's modifications
  are logical (axiom schemas, classically valid in every env);
  defeater's modifications are factual (defaults about a specific
  domain). The architectural pattern is the same — proposer presents a
  typed certificate, kernel admits or refuses — but the certificate's
  shape tracks what the substrate can support.

  The level-indexed conclusion relation `ConclAt T n` is forward
  chaining at rung n using only those rules that no admitted defeater
  (rung ≤ n) defeats. A defeater fires syntactically — its trigger is
  among the asserted facts up to its rung and none of its undercutters
  are. This sidesteps the negative-occurrence problem that would arise
  if defeaters fired on derived conclusions, while still exhibiting
  the level-indexed non-monotonicity the keynote needs.

  Headline: `Tower.rung_sound` — every rung is sound under the env
  that satisfies its facts and validates its undefeated rules.
-/

namespace Defeater

/-- A SoundDefeater certified within a fixed environment.

    Carries: the targeted rule, a trigger atom, optional undercutters
    (atoms whose presence prevents this defeater from firing), and the
    defeasibility certificate `defeats`. The certificate is a single
    proposition about `env`: when the trigger holds and no undercutter
    does, the targeted rule's conclusion fails. -/
structure SoundDefeater (env : Env) where
  rule : DefRule
  trigger : Atom
  undercutters : List Atom
  defeats : env trigger → (∀ u ∈ undercutters, ¬ env u) → ¬ env rule.concl

/-- A tower over `env`: a fixed list of rules, plus rung-indexed
    facts and defeaters certified against `env`. -/
structure Tower (env : Env) where
  rules : List DefRule
  /-- Facts admitted at exactly rung n (not cumulative). -/
  facts : Nat → List Atom
  /-- Defeaters admitted at exactly rung n (not cumulative). -/
  defs : Nat → List (SoundDefeater env)

namespace Tower

variable {env : Env}

/-- Cumulative facts up through rung n. -/
def factsUpTo (T : Tower env) : Nat → List Atom
  | 0     => T.facts 0
  | n + 1 => T.factsUpTo n ++ T.facts (n + 1)

/-- Cumulative defeaters up through rung n. -/
def defsUpTo (T : Tower env) : Nat → List (SoundDefeater env)
  | 0     => T.defs 0
  | n + 1 => T.defsUpTo n ++ T.defs (n + 1)

end Tower

/-- A defeater fires at rung n when its trigger is among the
    cumulative facts and no undercutter is. -/
def SoundDefeater.fires {env : Env} (d : SoundDefeater env)
    (T : Tower env) (n : Nat) : Prop :=
  d.trigger ∈ T.factsUpTo n ∧ ∀ u ∈ d.undercutters, u ∉ T.factsUpTo n

namespace Tower

variable {env : Env}

/-- A rule is undefeated at rung n iff no admitted defeater fires
    against it. -/
def isUndefeated (T : Tower env) (n : Nat) (r : DefRule) : Prop :=
  ∀ d ∈ T.defsUpTo n, d.rule = r → ¬ d.fires T n

/-- Conclusions at rung n: the level-indexed derivability relation.

    `fact` — anything asserted as a fact at rung ≤ n.
    `rule` — closure under any *undefeated* rule whose premises are
              concluded at rung n.

    The relation is non-monotone in n: a rule undefeated at rung n
    may become defeated at rung n+1 (new defeater admitted), and
    vice versa (new undercutter admitted). -/
inductive ConclAt (T : Tower env) (n : Nat) : Atom → Prop where
  | fact {a : Atom} : a ∈ T.factsUpTo n → ConclAt T n a
  | rule (r : DefRule) :
      r ∈ T.rules →
      T.isUndefeated n r →
      (∀ p ∈ r.prems, ConclAt T n p) →
      ConclAt T n r.concl

/-- Headline metatheorem (per-rung soundness).

    At every rung, conclusions hold under any env that:
    - satisfies the facts admitted up to that rung,
    - validates each rule that remains undefeated at that rung.

    The defeasibility certificates `d.defeats` are what the kernel
    checked at admission; they justify, in the env at hand, the
    second hypothesis below — undefeated rules really are valid in
    env. The proof is by induction over the derivation; each step is
    discharged either by the fact hypothesis or by the rule's
    validity. -/
theorem rung_sound {T : Tower env} {n : Nat}
    (hfacts : ∀ a ∈ T.factsUpTo n, env a)
    (hrules : ∀ r ∈ T.rules, T.isUndefeated n r → r.validUnder env)
    {a : Atom} (hc : ConclAt T n a) : env a := by
  induction hc with
  | fact h => exact hfacts _ h
  | rule r hr hund _ ih =>
    exact hrules r hr hund (fun p hp => ih p hp)

end Tower

end Defeater
