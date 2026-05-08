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

/-- **Conditional rung soundness.**

    At every rung, conclusions hold under any env that:
    - satisfies the facts admitted up to that rung,
    - validates each rule that remains undefeated at that rung.

    This theorem is *conditional* on the second hypothesis: it does
    not derive `r.validUnder env` for undefeated rules from the
    defeasibility certificates stored on each defeater. The kernel
    checked those certificates at admission, but to discharge the
    second hypothesis from them we need a coverage condition — see
    `undefeated_valid_under_coverage` below. -/
theorem rung_sound {T : Tower env} {n : Nat}
    (hfacts : ∀ a ∈ T.factsUpTo n, env a)
    (hrules : ∀ r ∈ T.rules, T.isUndefeated n r → r.validUnder env)
    {a : Atom} (hc : ConclAt T n a) : env a := by
  induction hc with
  | fact h => exact hfacts _ h
  | rule r hr hund _ ih =>
    exact hrules r hr hund (fun p hp => ih p hp)

/-- **Bridge theorem.** If every rule that fails to be valid under
    env has, at rung n, a firing defeater targeting it, then every
    rule undefeated at rung n is valid under env. Combined with
    `rung_sound`, this lets us discharge the second hypothesis from
    the certificates and a coverage condition.

    Proof: contrapositive. Suppose r is undefeated and ¬ r.validUnder env.
    Coverage gives us a firing defeater of r; isUndefeated says no
    such defeater exists; contradiction. -/
theorem undefeated_valid_under_coverage {T : Tower env} {n : Nat}
    (coverage : ∀ r ∈ T.rules, ¬ r.validUnder env →
      ∃ d ∈ T.defsUpTo n, d.rule = r ∧ d.fires T n) :
    ∀ r ∈ T.rules, T.isUndefeated n r → r.validUnder env := by
  intro r hr hund
  apply Classical.byContradiction
  intro h_inv
  obtain ⟨d, hd_mem, hd_rule, hd_fires⟩ := coverage r hr h_inv
  exact hund d hd_mem hd_rule hd_fires

/-! ## Stabilization

  When the tower has finite total height — i.e., no facts or
  defeaters are admitted past some rung K — the conclusion sequence
  `ConclAt T 0, ConclAt T 1, …` stabilizes at rung K. The "limit
  reasoner" coincides with the rung-K reasoner.

  Proof structure: empty admissions at rung n+1 leave factsUpTo,
  defsUpTo, fires, and isUndefeated unchanged from rung n; therefore
  ConclAt is the same inductive predicate; therefore conclusions are
  unchanged. Iterate.
-/

theorem factsUpTo_succ_of_empty {T : Tower env} {n : Nat}
    (hF : T.facts (n+1) = []) :
    T.factsUpTo (n+1) = T.factsUpTo n := by
  show T.factsUpTo n ++ T.facts (n+1) = T.factsUpTo n
  rw [hF]; simp

theorem defsUpTo_succ_of_empty {T : Tower env} {n : Nat}
    (hD : T.defs (n+1) = []) :
    T.defsUpTo (n+1) = T.defsUpTo n := by
  show T.defsUpTo n ++ T.defs (n+1) = T.defsUpTo n
  rw [hD]; simp

end Tower

theorem SoundDefeater.fires_succ_of_empty {env : Env} {T : Tower env} {n : Nat}
    (hF : T.facts (n+1) = []) (d : SoundDefeater env) :
    d.fires T (n+1) ↔ d.fires T n := by
  show (d.trigger ∈ T.factsUpTo (n+1) ∧ ∀ u ∈ d.undercutters, u ∉ T.factsUpTo (n+1))
     ↔ (d.trigger ∈ T.factsUpTo n ∧ ∀ u ∈ d.undercutters, u ∉ T.factsUpTo n)
  rw [Tower.factsUpTo_succ_of_empty hF]

namespace Tower

variable {env : Env}

theorem isUndefeated_succ_of_empty {T : Tower env} {n : Nat}
    (hF : T.facts (n+1) = []) (hD : T.defs (n+1) = []) (r : DefRule) :
    T.isUndefeated (n+1) r ↔ T.isUndefeated n r := by
  show (∀ d ∈ T.defsUpTo (n+1), d.rule = r → ¬ d.fires T (n+1))
     ↔ (∀ d ∈ T.defsUpTo n, d.rule = r → ¬ d.fires T n)
  rw [defsUpTo_succ_of_empty hD]
  constructor
  · intro h d hd hdr hf
    exact h d hd hdr ((SoundDefeater.fires_succ_of_empty hF d).mpr hf)
  · intro h d hd hdr hf
    exact h d hd hdr ((SoundDefeater.fires_succ_of_empty hF d).mp hf)

/-- One-step stabilization: if no new facts or defeaters are admitted
    at rung n+1, conclusions at rung n+1 coincide with conclusions at
    rung n. -/
theorem ConclAt_succ_of_empty {T : Tower env} {n : Nat}
    (hF : T.facts (n+1) = []) (hD : T.defs (n+1) = []) :
    ∀ a, ConclAt T (n+1) a ↔ ConclAt T n a := by
  intro a
  constructor
  · intro h
    induction h with
    | fact hmem =>
      apply ConclAt.fact
      rwa [factsUpTo_succ_of_empty hF] at hmem
    | rule r hr hund _hp ih =>
      apply ConclAt.rule r hr
      · exact (isUndefeated_succ_of_empty hF hD r).mp hund
      · exact ih
  · intro h
    induction h with
    | fact hmem =>
      apply ConclAt.fact
      rwa [factsUpTo_succ_of_empty hF]
    | rule r hr hund _hp ih =>
      apply ConclAt.rule r hr
      · exact (isUndefeated_succ_of_empty hF hD r).mpr hund
      · exact ih

/-- **Tower stabilization.** If the tower admits no facts or defeaters
    past rung K, the conclusion sequence is constant from rung K
    onward. The "limit reasoner" is the rung-K reasoner.

    This is the secondary metatheorem promised in the README: it
    grounds the keynote's framing of "the limit reasoner is the
    maximally-informed one" — once admissions stop, the conclusion
    set is fixed. -/
theorem tower_stabilizes {T : Tower env} (K : Nat)
    (hF : ∀ k, K < k → T.facts k = [])
    (hD : ∀ k, K < k → T.defs k = []) :
    ∀ n, K ≤ n → ∀ a, ConclAt T n a ↔ ConclAt T K a := by
  intro n
  induction n with
  | zero =>
    intro hn
    have : K = 0 := Nat.le_zero.mp hn
    subst this
    intro a; rfl
  | succ m ih =>
    intro hn a
    rcases Nat.eq_or_lt_of_le hn with hEq | hLt
    · subst hEq; rfl
    · have hKm : K ≤ m := Nat.lt_succ_iff.mp hLt
      have hF_m1 : T.facts (m+1) = [] := hF (m+1) (Nat.lt_succ_of_le hKm)
      have hD_m1 : T.defs (m+1) = [] := hD (m+1) (Nat.lt_succ_of_le hKm)
      rw [ConclAt_succ_of_empty hF_m1 hD_m1 a]
      exact ih hKm a

end Tower

end Defeater
