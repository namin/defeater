import Defeater.Tower

/-
  Defeater/Demo.lean — Tweety, end-to-end.

  Three rungs in the standard env "rocket-strapped penguin":
  - Rung 0: bird is asserted; the rule `bird ⇒ flies` is undefeated;
    `flies` is concluded.
  - Rung 1: penguin is asserted, plus a defeater of `bird ⇒ flies`
    triggered by penguin (and undercut by rocket). At rung 1, rocket
    is not yet asserted, so the defeater fires; `flies` is *not*
    concluded.
  - Rung 2: rocket is asserted. The penguin defeater is undercut, so
    `bird ⇒ flies` is undefeated again; `flies` is concluded once
    more.

  The conclusion sequence flips from "flies" to "no flies" to "flies":
  the level-indexed non-monotonicity the keynote needs, witnessed in
  Lean.
-/

namespace Defeater
namespace Demo

/-- The standard env: a rocket-strapped penguin who is also a bird
    and does fly. Atoms in the scenario are True; others are False. -/
def tweetyEnv : Env := fun a =>
  a = "bird" ∨ a = "penguin" ∨ a = "rocket" ∨ a = "flies"

/-- The (defeasible) rule: birds typically fly. -/
def birdFliesRule : DefRule :=
  { prems := ["bird"], concl := "flies" }

/-- The penguin defeater of `bird ⇒ flies`, undercut by rocket.

    The defeasibility certificate is vacuous in this env (rocket
    holds, so the "no undercutter" hypothesis cannot be satisfied).
    The kernel admits it as a typed term; the conclusion-flipping
    behavior shows up syntactically in the `Concl` proofs below. -/
def penguinDefeater : SoundDefeater tweetyEnv where
  rule := birdFliesRule
  trigger := "penguin"
  undercutters := ["rocket"]
  defeats := by
    intro _htrigger hUndercut _hconcl
    apply hUndercut "rocket"
    · simp
    · -- tweetyEnv "rocket" reduces to a disjunction; the rocket
      -- disjunct is provable by rfl.
      show "rocket" = "bird" ∨ "rocket" = "penguin" ∨
           "rocket" = "rocket" ∨ "rocket" = "flies"
      exact Or.inr (Or.inr (Or.inl rfl))

/-- The Tweety tower over `tweetyEnv`. -/
def tweetyTower : Tower tweetyEnv where
  rules := [birdFliesRule]
  facts := fun n => match n with
    | 0 => ["bird"]
    | 1 => ["penguin"]
    | 2 => ["rocket"]
    | _ => []
  defs := fun n => match n with
    | 1 => [penguinDefeater]
    | _ => []

/-- The cumulative facts at each rung, computed. -/
theorem factsUpTo_0 :
    Tower.factsUpTo tweetyTower 0 = ["bird"] := rfl

theorem factsUpTo_1 :
    Tower.factsUpTo tweetyTower 1 = ["bird", "penguin"] := rfl

theorem factsUpTo_2 :
    Tower.factsUpTo tweetyTower 2 = ["bird", "penguin", "rocket"] := rfl

/-- The cumulative defeaters at each rung. -/
theorem defsUpTo_0 :
    Tower.defsUpTo tweetyTower 0 = [] := rfl

theorem defsUpTo_1 :
    Tower.defsUpTo tweetyTower 1 = [penguinDefeater] := rfl

theorem defsUpTo_2 :
    Tower.defsUpTo tweetyTower 2 = [penguinDefeater] := rfl

/-- **Rung 0**: `flies` is concluded.

    The bird-flight rule is undefeated (no defeaters yet), and its
    premise `bird` is among the rung-0 facts. -/
theorem rung0_concludes_flies :
    Tower.ConclAt tweetyTower 0 "flies" := by
  apply Tower.ConclAt.rule birdFliesRule
  · -- birdFliesRule ∈ tweetyTower.rules
    show birdFliesRule ∈ [birdFliesRule]
    exact List.Mem.head _
  · -- isUndefeated 0 birdFliesRule: no defeaters at rung 0 to fire
    intro d hd _
    rw [defsUpTo_0] at hd
    cases hd
  · -- ∀ p ∈ ["bird"], ConclAt T 0 p
    intro p hp
    apply Tower.ConclAt.fact
    rw [factsUpTo_0]
    -- birdFliesRule.prems = ["bird"], hp says p ∈ ["bird"]
    exact hp

/-- **Rung 1**: `flies` is NOT concluded.

    The penguin defeater is admitted at rung 1; its trigger
    "penguin" is in the cumulative facts; its undercutter "rocket"
    is not (rocket is asserted at rung 2). So the defeater fires,
    and `bird ⇒ flies` is defeated. With no other rule and no
    "flies" fact, the atom is unconcluded.

    Proof generalizes "flies" to a fresh atom variable so the
    induction's `rule` case binds `r` without dependent-elimination
    issues; we then identify `r = birdFliesRule` and exhibit the
    firing defeater. -/
theorem rung1_no_flies :
    ¬ Tower.ConclAt tweetyTower 1 "flies" := by
  suffices h : ∀ a, Tower.ConclAt tweetyTower 1 a → a ≠ "flies" by
    intro hcon
    exact h "flies" hcon rfl
  intro a hca
  induction hca with
  | fact hmem =>
    intro hEq
    subst hEq
    rw [factsUpTo_1] at hmem
    simp at hmem
  | rule r hr hund _hp _ih =>
    intro _hEq
    -- The only rule in tweetyTower.rules is birdFliesRule.
    have hr_eq : r = birdFliesRule := by
      rw [show tweetyTower.rules = [birdFliesRule] from rfl] at hr
      cases hr with
      | head _ => rfl
      | tail _ h => cases h
    subst hr_eq
    -- penguinDefeater is admitted, targets birdFliesRule, and fires.
    have hd_mem : penguinDefeater ∈ tweetyTower.defsUpTo 1 := by
      rw [defsUpTo_1]; exact List.Mem.head _
    have hd_fires : penguinDefeater.fires tweetyTower 1 := by
      refine ⟨?_, ?_⟩
      · show "penguin" ∈ Tower.factsUpTo tweetyTower 1
        rw [factsUpTo_1]; decide
      · intro u hu
        have hu' : u ∈ ["rocket"] := hu
        have h_eq : u = "rocket" := by
          cases hu' with
          | head _ => rfl
          | tail _ h => cases h
        subst h_eq
        show "rocket" ∉ Tower.factsUpTo tweetyTower 1
        rw [factsUpTo_1]; decide
    exact hund penguinDefeater hd_mem rfl hd_fires

/-- **Rung 2**: `flies` is concluded again.

    The rocket undercutter is asserted at rung 2; the penguin
    defeater no longer fires; `bird ⇒ flies` is undefeated; the
    premise `bird` is still in the cumulative facts. -/
theorem rung2_concludes_flies :
    Tower.ConclAt tweetyTower 2 "flies" := by
  apply Tower.ConclAt.rule birdFliesRule
  · show birdFliesRule ∈ [birdFliesRule]
    exact List.Mem.head _
  · -- isUndefeated 2 birdFliesRule: penguinDefeater no longer fires.
    intro d hd _hr_eq hfires
    rw [defsUpTo_2] at hd
    have hd_eq : d = penguinDefeater := by
      cases hd with
      | head _ => rfl
      | tail _ h => cases h
    subst hd_eq
    -- penguinDefeater.fires tweetyTower 2 demands rocket ∉ factsUpTo 2,
    -- but rocket IS asserted at rung 2.
    obtain ⟨_, hNoUndercut⟩ := hfires
    apply hNoUndercut "rocket" (List.Mem.head _)
    rw [factsUpTo_2]
    simp
  · -- ∀ p ∈ ["bird"], ConclAt T 2 p
    intro p hp
    apply Tower.ConclAt.fact
    rw [factsUpTo_2]
    -- p ∈ ["bird"] means p = "bird"; "bird" is in factsUpTo 2.
    cases hp with
    | head _ => simp
    | tail _ h => cases h

end Demo
end Defeater
