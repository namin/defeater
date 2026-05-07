import Defeater.Demo

/-
  Defeater/Counter.lean — separating witnesses for non-monotonicity.

  The Tweety tower's conclusion sequence isn't merely level-indexed
  (the kernel admits more defeaters with each rung) — it is
  genuinely non-monotone in the rung index: some atom is concluded
  at rung m, *not* concluded at rung n > m, and concluded again at
  rung k > n. The theorems below assemble the three Demo-proofs
  into the standard non-monotonicity witnesses.
-/

namespace Defeater
namespace Counter

open Demo

/-- The conclusion sequence for `flies`: present at rung 0, absent
    at rung 1, present again at rung 2. The "oscillation" the
    keynote points at: a rung can both lose and recover a
    conclusion under proposer/gate-controlled defeater admission. -/
theorem flies_oscillates :
    Tower.ConclAt tweetyTower 0 "flies" ∧
    ¬ Tower.ConclAt tweetyTower 1 "flies" ∧
    Tower.ConclAt tweetyTower 2 "flies" :=
  ⟨rung0_concludes_flies, rung1_no_flies, rung2_concludes_flies⟩

/-- Descent: there exist rungs m < n where the lower rung concludes
    an atom that the higher rung does not. Witnesses: m = 0, n = 1. -/
theorem descent_witness :
    ∃ m n : Nat,
      m < n ∧
      Tower.ConclAt tweetyTower m "flies" ∧
      ¬ Tower.ConclAt tweetyTower n "flies" :=
  ⟨0, 1, by decide, rung0_concludes_flies, rung1_no_flies⟩

/-- Ascent: there exist rungs m < n where the higher rung concludes
    an atom that the lower rung does not. Witnesses: m = 1, n = 2. -/
theorem ascent_witness :
    ∃ m n : Nat,
      m < n ∧
      ¬ Tower.ConclAt tweetyTower m "flies" ∧
      Tower.ConclAt tweetyTower n "flies" :=
  ⟨1, 2, by decide, rung1_no_flies, rung2_concludes_flies⟩

/-- The conclusion-set function `n ↦ {a | ConclAt T n a}` is NOT
    monotone in `n`: rung 0 contains `flies` while rung 1 does not.
    This is the syntactic witness that defeaters are doing real
    semantic work — not merely indexing the same conclusion set. -/
theorem conclusions_not_monotone :
    ∃ m n : Nat,
      m < n ∧ ∃ a : Atom,
        Tower.ConclAt tweetyTower m a ∧ ¬ Tower.ConclAt tweetyTower n a :=
  ⟨0, 1, by decide, "flies", rung0_concludes_flies, rung1_no_flies⟩

/-- The Tweety tower has finite total height: nothing is admitted
    past rung 2. -/
theorem tweetyTower_facts_empty_past_2 :
    ∀ k, 2 < k → tweetyTower.facts k = [] := by
  intro k hk
  match k, hk with
  | _ + 3, _ => rfl

theorem tweetyTower_defs_empty_past_2 :
    ∀ k, 2 < k → tweetyTower.defs k = [] := by
  intro k hk
  match k, hk with
  | _ + 3, _ => rfl

/-- Tweety's conclusion sequence stabilizes at rung 2: the limit
    reasoner is the rung-2 reasoner. A direct application of the
    general `tower_stabilizes` metatheorem to this concrete tower. -/
theorem tweetyTower_stabilizes :
    ∀ n, 2 ≤ n → ∀ a,
      Tower.ConclAt tweetyTower n a ↔ Tower.ConclAt tweetyTower 2 a :=
  Tower.tower_stabilizes 2
    tweetyTower_facts_empty_past_2
    tweetyTower_defs_empty_past_2

end Counter
end Defeater
