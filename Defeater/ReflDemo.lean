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

end ReflDemo
end Defeater
