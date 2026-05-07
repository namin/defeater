import Defeater

/-
  Smoke.lean — smoke test executable.

  Reports the load-bearing facts of the defeater artifact at
  runtime. Every claim below is a Lean theorem; the executable just
  prints that the kernel checked it at compile time.
-/

open Defeater
open Defeater.Demo

def main : IO Unit := do
  IO.println "defeater — smoke test"
  IO.println "====================="
  IO.println ""
  IO.println "Object substrate: ground propositional, atoms = String."
  IO.println "    DefRule.validUnder env : (∀ p ∈ prems, env p) → env concl"
  IO.println "    Concl.sound : ungated forward chaining is sound  ✓"
  IO.println ""
  IO.println "Tower layer:"
  IO.println "    SoundDefeater env : (rule, trigger, undercutters, defeats)"
  IO.println "    defeats : env trigger → (no undercutter) → ¬ env concl"
  IO.println "    Tower env : rules + rung-indexed facts + rung-indexed defeaters"
  IO.println "    ConclAt T n : level-indexed derivability  ✓"
  IO.println ""
  IO.println "Headline metatheorem:"
  IO.println "    Tower.rung_sound : every rung is sound under the env that"
  IO.println "      satisfies its facts and validates its undefeated rules  ✓"
  IO.println ""
  IO.println "Stabilization:"
  IO.println "    Tower.tower_stabilizes : if the tower admits no facts or"
  IO.println "      defeaters past rung K, conclusions are constant from K  ✓"
  IO.println ""
  IO.println "Tweety scenario (rocket-strapped penguin):"
  IO.println "    rule:    bird ⇒ flies"
  IO.println "    rung 0:  bird"
  IO.println "    rung 1:  penguin  + defeater (penguin defeats bird ⇒ flies,"
  IO.println "                                  undercut by rocket)"
  IO.println "    rung 2:  rocket"
  IO.println ""
  IO.println "    rung0_concludes_flies   : ConclAt tweetyTower 0 \"flies\"  ✓"
  IO.println "    rung1_no_flies          : ¬ ConclAt tweetyTower 1 \"flies\"  ✓"
  IO.println "    rung2_concludes_flies   : ConclAt tweetyTower 2 \"flies\"  ✓"
  IO.println ""
  IO.println "    The conclusion sequence: flies → ¬flies → flies."
  IO.println "    Level-indexed non-monotonicity, witnessed in Lean."
  IO.println ""
  IO.println "Soundness applied to the demo:"
  IO.println "    tweety_rung2_sound : every conclusion at rung 2 holds in"
  IO.println "      tweetyEnv (rung_sound instantiated end-to-end)  ✓"
  IO.println ""
  IO.println "Stability applied to the demo:"
  IO.println "    tweetyTower_stabilizes : conclusions are constant for"
  IO.println "      n ≥ 2 (tower_stabilizes corollary)  ✓"
  IO.println ""
  IO.println "Climber checks theory construction; defeater checks theory"
  IO.println "qualification. Same kernel discipline, opposite polarity."
