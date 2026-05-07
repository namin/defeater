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

end Counter
end Defeater
