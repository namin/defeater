import Defeater.Reflection

/-
  Defeater/Oscillate.lean — reflective non-stabilization.

  The syntactic stabilization theorem (`Tower.tower_stabilizes`)
  says that once admissions stop, the conclusion sequence is
  constant. That theorem does NOT lift unconditionally to the
  reflective layer. This file constructs the counterexample.

  The tower:
    rules:    R : z ⇒ x        R' : x ⇒ y
    defeater: D : target R', trigger y, no undercutters
    facts:    z at rung 0
    defs:     D at rung 0
    no further admissions at any later rung

  Behavior of the conclusion sequence:
    rung 0 (no defeaters fire — baseline): closure of {z} under
      both rules gives {z, x, y}. So `y` IS concluded at rung 0.
    rung 1: D fires reflectively because `y ∈ ReflConclAt T 0`.
      R' is defeated. Closure gives {z, x}. `y` is NOT concluded.
    rung 2: D doesn't fire because `y ∉ ReflConclAt T 1`. R' is
      undefeated. Closure gives {z, x, y}. `y` IS concluded again.

  No new admissions ever happen, yet the conclusion sequence
  oscillates with period 2. The syntactic stabilization theorem's
  hypothesis is satisfied (admissions stop at rung 0, so K = 0)
  but the reflective conclusion doesn't stabilize.

  This makes precise *why* the reflective layer is genuinely
  different from the syntactic one — the active predicate at each
  rung depends on the prior rung's conclusions, creating feedback
  loops that syntactic firing cannot have.
-/

namespace Defeater
namespace Oscillate

/-- Standard env. `y` is False so the defeasibility certificate
    holds (`env y` is false ⇒ `¬ env y` is trivially true). -/
def oscEnv : Env := fun a =>
  match a with
  | "z" => True
  | "x" => True
  | "y" => False
  | _   => False

def ruleR : DefRule := { prems := ["z"], concl := "x" }

def ruleR' : DefRule := { prems := ["x"], concl := "y" }

/-- A self-feedback defeater: triggers on `y`, defeats `R'` whose
    conclusion is `y`. Whenever `y` is concluded at the prior rung,
    the rule that produces it gets defeated at the next rung. -/
def yDefeater : SoundDefeater oscEnv where
  rule := ruleR'
  trigger := "y"
  undercutters := []
  defeats := by
    intro htrigger _ _
    exact htrigger

/-- The oscillating tower: all admissions at rung 0. -/
def oscTower : Tower oscEnv where
  rules := [ruleR, ruleR']
  facts := fun n => match n with
    | 0 => ["z"]
    | _ => []
  defs := fun n => match n with
    | 0 => [yDefeater]
    | _ => []

/-- The cumulative facts are `["z"]` at every rung — only rung 0
    contributes facts. -/
theorem osc_factsUpTo_eq (n : Nat) :
    Tower.factsUpTo oscTower n = ["z"] := by
  induction n with
  | zero => rfl
  | succ m ih =>
    show Tower.factsUpTo oscTower m ++ oscTower.facts (m + 1) = ["z"]
    have : oscTower.facts (m + 1) = [] := rfl
    rw [this, ih]
    rfl

/-- The cumulative defeaters are `[yDefeater]` at every rung — only
    rung 0 contributes defeaters. -/
theorem osc_defsUpTo_eq (n : Nat) :
    Tower.defsUpTo oscTower n = [yDefeater] := by
  induction n with
  | zero => rfl
  | succ m ih =>
    show Tower.defsUpTo oscTower m ++ oscTower.defs (m + 1) = [yDefeater]
    have : oscTower.defs (m + 1) = [] := rfl
    rw [this, ih]
    rfl

/-- At any rung, `z` is in the cumulative facts. -/
theorem any_factsUpTo_z (n : Nat) :
    "z" ∈ Tower.factsUpTo oscTower n := by
  rw [osc_factsUpTo_eq]
  exact List.Mem.head _

/-- `R` is undefeated at every rung — no defeater targets it. -/
theorem ruleR_undefeated_at (n : Nat) :
    Tower.isUndefeatedRefl oscTower n ruleR := by
  cases n with
  | zero => trivial
  | succ m =>
    intro d hd hdr
    rw [osc_defsUpTo_eq] at hd
    have hd_eq : d = yDefeater := by
      cases hd with
      | head _ => rfl
      | tail _ h => cases h
    subst hd_eq
    -- hdr : yDefeater.rule = ruleR; but yDefeater.rule = ruleR'
    exact absurd hdr (by decide)

/-- The Closure form of "z is concluded at rung n". A helper for use
    inside other Closure constructions. -/
theorem any_concludes_z_cl (n : Nat) :
    Closure oscTower.rules (Tower.isUndefeatedRefl oscTower n)
      (Tower.factsUpTo oscTower n) "z" := by
  apply Closure.fact
  exact any_factsUpTo_z n

/-- `z` is concluded at every rung. -/
theorem any_concludes_z (n : Nat) :
    Tower.ReflConclAt oscTower n "z" := by
  rw [Tower.reflConclAt_eq]
  exact any_concludes_z_cl n

/-- `x` is concluded at every rung — `R` is always active and its
    premise `z` is always available. -/
theorem any_concludes_x_cl (n : Nat) :
    Closure oscTower.rules (Tower.isUndefeatedRefl oscTower n)
      (Tower.factsUpTo oscTower n) "x" := by
  apply Closure.rule ruleR
  · show ruleR ∈ [ruleR, ruleR']
    exact List.Mem.head _
  · exact ruleR_undefeated_at n
  · intro p hp
    cases hp with
    | head _ => exact any_concludes_z_cl n
    | tail _ h => cases h

theorem any_concludes_x (n : Nat) :
    Tower.ReflConclAt oscTower n "x" := by
  rw [Tower.reflConclAt_eq]
  exact any_concludes_x_cl n

/-- **Rung 0 concludes `y`**: baseline closure under both rules. -/
theorem rung0_concludes_y :
    Tower.ReflConclAt oscTower 0 "y" := by
  show Closure oscTower.rules (fun _ => True)
       (Tower.factsUpTo oscTower 0) "y"
  apply Closure.rule ruleR'
  · show ruleR' ∈ [ruleR, ruleR']
    exact List.Mem.tail _ (List.Mem.head _)
  · trivial
  · intro p hp
    cases hp with
    | head _ =>
      apply Closure.rule ruleR
      · exact List.Mem.head _
      · trivial
      · intro p' hp'
        cases hp' with
        | head _ =>
          apply Closure.fact
          exact any_factsUpTo_z 0
        | tail _ h => cases h
    | tail _ h => cases h

/-- **Rung 1 does NOT conclude `y`**: yDefeater fires reflectively
    (because `y ∈ ReflConclAt T 0`), defeating `R'`. No other rule
    produces `y`, and `y` isn't a fact. -/
theorem rung1_no_y :
    ¬ Tower.ReflConclAt oscTower 1 "y" := by
  intro hc
  rw [Tower.reflConclAt_eq] at hc
  suffices h : ∀ a,
      Closure oscTower.rules (Tower.isUndefeatedRefl oscTower 1)
        (Tower.factsUpTo oscTower 1) a → a ≠ "y" by
    exact h "y" hc rfl
  intro a hca
  induction hca with
  | fact hmem =>
    intro hEq
    subst hEq
    rw [osc_factsUpTo_eq] at hmem
    exact absurd hmem (by decide)
  | rule r hr hact _hp _ih =>
    cases hr with
    | head _ =>
      -- r = ruleR; ruleR.concl = "x" ≠ "y"
      decide
    | tail _ h =>
      cases h with
      | head _ =>
        -- r = ruleR'; ruleR'.concl = "y". Defeater fires; contradict hact.
        intro _hEq
        apply hact yDefeater
          (by rw [osc_defsUpTo_eq]; exact List.Mem.head _)
          rfl
        refine ⟨rung0_concludes_y, ?_⟩
        intro u hu
        cases hu
      | tail _ h' => cases h'

/-- **Rung 2 concludes `y` again**: `y ∉ ReflConclAt T 1`, so
    yDefeater doesn't fire at rung 2; `R'` is undefeated; closure
    re-derives `y` from `x`. The conclusion sequence has come back
    up — it oscillates. -/
theorem rung2_concludes_y :
    Tower.ReflConclAt oscTower 2 "y" := by
  rw [Tower.reflConclAt_eq]
  apply Closure.rule ruleR'
  · show ruleR' ∈ [ruleR, ruleR']
    exact List.Mem.tail _ (List.Mem.head _)
  · -- isUndefeatedRefl T 2 ruleR': only yDefeater targets it, and
    -- yDefeater doesn't fire at rung 2 because y ∉ ReflConclAt T 1.
    intro d hd _hdr
    rw [osc_defsUpTo_eq] at hd
    have : d = yDefeater := by
      cases hd with
      | head _ => rfl
      | tail _ h => cases h
    subst this
    intro ⟨hY, _⟩
    exact rung1_no_y hY
  · intro p hp
    cases hp with
    | head _ => exact any_concludes_x_cl 2
    | tail _ h => cases h

/-- **Period-2 oscillation, three rungs witnessed.** No new
    admissions happen past rung 0, yet `y` is concluded, then not,
    then concluded again — the syntactic stabilization theorem's
    conclusion (constant from rung 0 onward) FAILS for the
    reflective semantics.

    This is the structural counterexample: the active predicate at
    each rung depends on the prior rung's conclusions, creating a
    feedback loop that the syntactic firing-on-facts version cannot
    exhibit. -/
theorem reflective_oscillation :
    Tower.ReflConclAt oscTower 0 "y" ∧
    ¬ Tower.ReflConclAt oscTower 1 "y" ∧
    Tower.ReflConclAt oscTower 2 "y" :=
  ⟨rung0_concludes_y, rung1_no_y, rung2_concludes_y⟩

end Oscillate
end Defeater
