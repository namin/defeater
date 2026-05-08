import Defeater.Reflection

/-
  Defeater/ReflDemo.lean — reflective Tweety, end-to-end.

  Two rules:
    R1 : bird ⇒ flies          (default rule, target of defeating)
    R2 : penguin ⇒ cantFly     (chains penguinhood to inability to fly)

  Tower:
    rung 0: facts {bird, penguin}; no defeaters fire (rung 0 is the
            baseline). Both R1 and R2 apply, so the rung-0 conclusion
            set contains `flies` AND `cantFly`. Note `cantFly` is
            *derived* — it isn't in the asserted facts, R2 produces it.
    rung 1: a defeater of R1 with trigger `cantFly`. The defeater
            fires *reflectively* — it looks at what was concluded at
            rung 0 and finds `cantFly`. R1 is defeated; `flies` is
            no longer concluded at rung 1. R2 stays active so
            `cantFly` is still concluded.

  This is the keynote claim made concrete: the upper rung observes
  the lower rung's *inferences* (cantFly was derived, not asserted)
  and intervenes. The syntactic-firing version of Tweety can't tell
  this story — its defeater fires on a primitive assertion.
-/

namespace Defeater
namespace ReflDemo

/-- Standard env: penguins are non-flying birds. -/
def reflEnv : Env := fun a =>
  match a with
  | "bird"    => True
  | "penguin" => True
  | "cantFly" => True
  | "flies"   => False
  | _         => False

def birdFliesRule : DefRule :=
  { prems := ["bird"], concl := "flies" }

def penguinCantFlyRule : DefRule :=
  { prems := ["penguin"], concl := "cantFly" }

/-- Defeater of `bird ⇒ flies`, triggered REFLECTIVELY by `cantFly`.
    `cantFly` is derived (not asserted) at rung 0; the defeater at
    rung 1 fires based on that derivation. -/
def cantFlyDefeater : SoundDefeater reflEnv where
  rule := birdFliesRule
  trigger := "cantFly"
  undercutters := []
  defeats := by
    intro _htrigger _hUC hflies
    -- reflEnv "flies" reduces definitionally to False; hflies : False
    exact hflies

/-- The tower for the reflective Tweety demo. -/
def reflTower : Tower reflEnv where
  rules := [birdFliesRule, penguinCantFlyRule]
  facts := fun n => match n with
    | 0 => ["bird", "penguin"]
    | _ => []
  defs := fun n => match n with
    | 1 => [cantFlyDefeater]
    | _ => []

/-- Cumulative facts: rung 0 admits `bird, penguin`; nothing later. -/
theorem refl_factsUpTo_0 :
    Tower.factsUpTo reflTower 0 = ["bird", "penguin"] := rfl

theorem refl_factsUpTo_1 :
    Tower.factsUpTo reflTower 1 = ["bird", "penguin"] := rfl

theorem refl_defsUpTo_1 :
    Tower.defsUpTo reflTower 1 = [cantFlyDefeater] := rfl

/-- **Rung 0 derives `cantFly`.** R2 produces it from the asserted
    fact `penguin`. This conclusion is what the rung-1 defeater will
    observe reflectively. -/
theorem rung0_concludes_cantFly :
    Tower.ReflConclAt reflTower 0 "cantFly" := by
  show Closure reflTower.rules (fun _ => True)
       (Tower.factsUpTo reflTower 0) "cantFly"
  apply Closure.rule penguinCantFlyRule
  · -- penguinCantFlyRule ∈ reflTower.rules
    show penguinCantFlyRule ∈ [birdFliesRule, penguinCantFlyRule]
    exact List.Mem.tail _ (List.Mem.head _)
  · trivial
  · intro p hp
    apply Closure.fact
    cases hp with
    | head _ =>
      rw [refl_factsUpTo_0]
      exact List.Mem.tail _ (List.Mem.head _)
    | tail _ h => cases h

/-- **Rung 0 derives `flies`.** R1 produces it from the asserted
    fact `bird`. No defeaters fire at rung 0. -/
theorem rung0_concludes_flies :
    Tower.ReflConclAt reflTower 0 "flies" := by
  show Closure reflTower.rules (fun _ => True)
       (Tower.factsUpTo reflTower 0) "flies"
  apply Closure.rule birdFliesRule
  · show birdFliesRule ∈ [birdFliesRule, penguinCantFlyRule]
    exact List.Mem.head _
  · trivial
  · intro p hp
    apply Closure.fact
    cases hp with
    | head _ =>
      rw [refl_factsUpTo_0]
      exact List.Mem.head _
    | tail _ h => cases h

/-- **Rung 1 does NOT conclude `flies`.** The defeater fires
    reflectively on `cantFly` (which was concluded at rung 0 via R2).
    `bird ⇒ flies` is defeated; no other rule produces `flies`; and
    `flies` is not in the cumulative facts. -/
theorem rung1_no_flies :
    ¬ Tower.ReflConclAt reflTower 1 "flies" := by
  intro hc
  rw [Tower.reflConclAt_eq] at hc
  -- Generalize the conclusion atom for the induction.
  suffices h : ∀ a, Closure reflTower.rules (Tower.isUndefeatedRefl reflTower 1)
                      (Tower.factsUpTo reflTower 1) a → a ≠ "flies" by
    exact h "flies" hc rfl
  intro a hca
  induction hca with
  | fact hmem =>
    intro hEq
    subst hEq
    rw [refl_factsUpTo_1] at hmem
    exact absurd hmem (by decide)
  | rule r hr hact _hp _ih =>
    cases hr with
    | head _ =>
      -- r = birdFliesRule. Goal: "flies" ≠ "flies". Derive False from
      -- hact, since cantFlyDefeater fires reflectively at rung 1.
      intro _hEq
      apply hact cantFlyDefeater
        (by rw [refl_defsUpTo_1]; exact List.Mem.head _)
        rfl
      refine ⟨rung0_concludes_cantFly, ?_⟩
      intro u hu
      cases hu
    | tail _ h =>
      cases h with
      | head _ =>
        -- r = penguinCantFlyRule, r.concl = "cantFly" ≠ "flies"
        decide
      | tail _ h' => cases h'

/-- **Rung 1 still concludes `cantFly`.** R2 isn't defeated by
    cantFlyDefeater (which targets R1, not R2), so it still fires.
    Conclusion: defeating R1 doesn't disturb conclusions reached by
    other rules. -/
theorem rung1_concludes_cantFly :
    Tower.ReflConclAt reflTower 1 "cantFly" := by
  rw [Tower.reflConclAt_eq]
  apply Closure.rule penguinCantFlyRule
  · show penguinCantFlyRule ∈ [birdFliesRule, penguinCantFlyRule]
    exact List.Mem.tail _ (List.Mem.head _)
  · -- isUndefeatedRefl T 1 penguinCantFlyRule: cantFlyDefeater targets
    -- birdFliesRule, not penguinCantFlyRule, so it doesn't apply here.
    intro d hd hdr
    rw [refl_defsUpTo_1] at hd
    cases hd with
    | head _ =>
      -- d = cantFlyDefeater; hdr : cantFlyDefeater.rule = penguinCantFlyRule
      -- but cantFlyDefeater.rule = birdFliesRule, contradiction.
      exact absurd hdr (by decide)
    | tail _ h => cases h
  · intro p hp
    apply Closure.fact
    cases hp with
    | head _ =>
      rw [refl_factsUpTo_1]
      exact List.Mem.tail _ (List.Mem.head _)
    | tail _ h => cases h

/-! ## End-to-end soundness via the bridge theorem

  Here the certificates *earn their keep*: `birdFliesRule` is
  *invalid* under `reflEnv` (env "bird" = T, env "flies" = F), and
  the coverage condition at rung 1 produces the cantFlyDefeater as
  its firing witness. Combined with `refl_undefeated_valid_under_coverage`
  and `refl_rung_sound`, this yields end-to-end soundness without
  postulating rule-validity by hand. -/

/-- `reflEnv` satisfies the facts admitted up through rung 1. -/
theorem reflEnv_satisfies_factsUpTo_1 :
    ∀ a ∈ Tower.factsUpTo reflTower 1, reflEnv a := by
  intro a ha
  rw [refl_factsUpTo_1] at ha
  cases ha with
  | head _ => trivial
  | tail _ h =>
    cases h with
    | head _ => trivial
    | tail _ h' => cases h'

/-- `birdFliesRule` is *not* valid under `reflEnv`: env "bird" holds
    but env "flies" doesn't. The defeasible rule fails its semantic
    test in this env. -/
theorem birdFliesRule_invalid : ¬ birdFliesRule.validUnder reflEnv := by
  intro hvalid
  -- Apply to the prems hypothesis (env "bird" = True) to get env "flies",
  -- which reduces definitionally to False.
  exact hvalid (fun p hp => by
    cases hp with
    | head _ => trivial
    | tail _ h => cases h)

/-- `penguinCantFlyRule` *is* valid under `reflEnv`: env "penguin" → env "cantFly". -/
theorem penguinCantFlyRule_valid : penguinCantFlyRule.validUnder reflEnv := by
  intro _; trivial

/-- **Coverage at rung 1.** Every env-invalid rule has a reflectively
    firing defeater. The only invalid rule is `birdFliesRule`, and
    `cantFlyDefeater` targets it with trigger `cantFly`, which was
    concluded at rung 0 via `penguinCantFlyRule`. -/
theorem refl_coverage_at_rung_1 :
    ∀ r ∈ reflTower.rules, ¬ r.validUnder reflEnv →
      ∃ d ∈ Tower.defsUpTo reflTower 1,
        d.rule = r ∧
        Tower.ReflConclAt reflTower 0 d.trigger ∧
        (∀ u ∈ d.undercutters, ¬ Tower.ReflConclAt reflTower 0 u) := by
  intro r hr hinv
  -- r ∈ [birdFliesRule, penguinCantFlyRule]; only birdFliesRule is invalid.
  cases hr with
  | head _ =>
    -- r = birdFliesRule
    refine ⟨cantFlyDefeater, ?_, rfl, rung0_concludes_cantFly, ?_⟩
    · rw [refl_defsUpTo_1]; exact List.Mem.head _
    · intro u hu; cases hu
  | tail _ h =>
    cases h with
    | head _ =>
      -- r = penguinCantFlyRule, but it IS valid — coverage hypothesis vacuous.
      exact absurd penguinCantFlyRule_valid hinv
    | tail _ h' => cases h'

/-- **End-to-end rung-1 soundness for the reflective Tweety demo.**
    Every conclusion at rung 1 holds in `reflEnv`. The certificates
    do real work here: the `cantFlyDefeater`'s defeasibility
    certificate, combined with the coverage condition, discharges
    the validity hypothesis of `refl_rung_sound`. -/
theorem reflDemo_rung1_sound :
    ∀ a, Tower.ReflConclAt reflTower 1 a → reflEnv a := by
  intro a hc
  exact Tower.refl_rung_sound
    reflEnv_satisfies_factsUpTo_1
    (Tower.refl_undefeated_valid_under_coverage refl_coverage_at_rung_1)
    hc

end ReflDemo
end Defeater
