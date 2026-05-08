import Defeater.Reflection

/-
  Defeater/Nixon.lean — the Nixon Diamond.

  The textbook example of *symmetric defeasible conflict* (Reiter,
  McCarthy, ubiquitous since the 1980s):

    Quaker     ⇒ pacifist
    Republican ⇒ nonpacifist
    Nixon is both Quaker and Republican.

  Standard defeasible-logic readings:
  - *Skeptical*: conclude neither — the conflicting defaults block
    each other.
  - *Credulous*: there are two consistent extensions, one with
    pacifist, one with nonpacifist.
  - *Specificity-based*: if no priority order is given, neither wins.

  Our minimal substrate has no priorities and no negation. We model
  the conflict via two rules and two rebutting defeaters: each rule's
  conclusion is the other defeater's trigger. Reflectively this is
  the same shape as `Oscillate.lean` — the conclusion sequence
  oscillates with period 2:

    rung 0:  both concluded (no defeaters fire — baseline)
    rung 1:  neither concluded (each defeater fires reflectively
             on the other rule's rung-0 conclusion)
    rung 2:  both concluded again (neither was concluded at rung 1,
             so no defeater fires; both rules undefeated)

  Skeptical reading lives at rung 1; credulous reading lives at
  rung 0 (or rung 2). The framework refuses to choose. That refusal
  IS the textbook content — Nixon Diamond is the canonical case
  where defeasible logic has no preferred answer.
-/

namespace Defeater
namespace Nixon

/-- Standard env: `pacifist` and `nonpacifist` are both False. The
    defeasibility certificates hold vacuously (when env concl is
    False, ¬ env concl is True). -/
def nixonEnv : Env := fun a =>
  match a with
  | "quaker"      => True
  | "republican"  => True
  | "pacifist"    => False
  | "nonpacifist" => False
  | _             => False

def quakerRule : DefRule :=
  { prems := ["quaker"], concl := "pacifist" }

def republicanRule : DefRule :=
  { prems := ["republican"], concl := "nonpacifist" }

/-- Defeater of `Quaker ⇒ pacifist`, triggered by the *other* rule's
    conclusion `nonpacifist`. -/
def quakerDefeater : SoundDefeater nixonEnv where
  rule := quakerRule
  trigger := "nonpacifist"
  undercutters := []
  defeats := by
    intro _ _ hpacifist
    -- nixonEnv "pacifist" reduces to False; hpacifist : False.
    exact hpacifist

/-- Defeater of `Republican ⇒ nonpacifist`, triggered by `pacifist`. -/
def republicanDefeater : SoundDefeater nixonEnv where
  rule := republicanRule
  trigger := "pacifist"
  undercutters := []
  defeats := by
    intro _ _ hnonpacifist
    exact hnonpacifist

/-- The Nixon Diamond tower: all admissions at rung 0. -/
def nixonTower : Tower nixonEnv where
  rules := [quakerRule, republicanRule]
  facts := fun n => match n with
    | 0 => ["quaker", "republican"]
    | _ => []
  defs := fun n => match n with
    | 0 => [quakerDefeater, republicanDefeater]
    | _ => []

/-- Cumulative facts are `["quaker", "republican"]` at every rung. -/
theorem nixon_factsUpTo_eq (n : Nat) :
    Tower.factsUpTo nixonTower n = ["quaker", "republican"] := by
  induction n with
  | zero => rfl
  | succ m ih =>
    show Tower.factsUpTo nixonTower m ++ nixonTower.facts (m + 1) =
         ["quaker", "republican"]
    have : nixonTower.facts (m + 1) = [] := rfl
    rw [this, ih]
    rfl

/-- Cumulative defeaters are both at every rung. -/
theorem nixon_defsUpTo_eq (n : Nat) :
    Tower.defsUpTo nixonTower n = [quakerDefeater, republicanDefeater] := by
  induction n with
  | zero => rfl
  | succ m ih =>
    show Tower.defsUpTo nixonTower m ++ nixonTower.defs (m + 1) =
         [quakerDefeater, republicanDefeater]
    have : nixonTower.defs (m + 1) = [] := rfl
    rw [this, ih]
    rfl

/-- **Rung 0 concludes `pacifist`**: baseline — `Quaker ⇒ pacifist`
    fires from the asserted Quaker fact, no defeaters yet. -/
theorem rung0_concludes_pacifist :
    Tower.ReflConclAt nixonTower 0 "pacifist" := by
  show Closure nixonTower.rules (fun _ => True)
       (Tower.factsUpTo nixonTower 0) "pacifist"
  apply Closure.rule quakerRule
  · show quakerRule ∈ [quakerRule, republicanRule]
    exact List.Mem.head _
  · trivial
  · intro p hp
    cases hp with
    | head _ =>
      apply Closure.fact
      rw [nixon_factsUpTo_eq]
      exact List.Mem.head _
    | tail _ h => cases h

/-- **Rung 0 concludes `nonpacifist`**: symmetrically, `Republican ⇒
    nonpacifist` fires. -/
theorem rung0_concludes_nonpacifist :
    Tower.ReflConclAt nixonTower 0 "nonpacifist" := by
  show Closure nixonTower.rules (fun _ => True)
       (Tower.factsUpTo nixonTower 0) "nonpacifist"
  apply Closure.rule republicanRule
  · show republicanRule ∈ [quakerRule, republicanRule]
    exact List.Mem.tail _ (List.Mem.head _)
  · trivial
  · intro p hp
    cases hp with
    | head _ =>
      apply Closure.fact
      rw [nixon_factsUpTo_eq]
      exact List.Mem.tail _ (List.Mem.head _)
    | tail _ h => cases h

/-- **Rung 1 does NOT conclude `pacifist`**: quakerDefeater fires
    reflectively (because `nonpacifist ∈ ReflConclAt T 0`),
    defeating `Quaker ⇒ pacifist`. No other rule produces pacifist. -/
theorem rung1_no_pacifist :
    ¬ Tower.ReflConclAt nixonTower 1 "pacifist" := by
  intro hc
  rw [Tower.reflConclAt_eq] at hc
  suffices h : ∀ a,
      Closure nixonTower.rules (Tower.isUndefeatedRefl nixonTower 1)
        (Tower.factsUpTo nixonTower 1) a → a ≠ "pacifist" by
    exact h "pacifist" hc rfl
  intro a hca
  induction hca with
  | fact hmem =>
    intro hEq
    subst hEq
    rw [nixon_factsUpTo_eq] at hmem
    exact absurd hmem (by decide)
  | rule r hr hact _hp _ih =>
    cases hr with
    | head _ =>
      -- r = quakerRule; concl = "pacifist". Defeater fires; contradict hact.
      intro _hEq
      apply hact quakerDefeater
        (by rw [nixon_defsUpTo_eq]; exact List.Mem.head _)
        rfl
      refine ⟨rung0_concludes_nonpacifist, ?_⟩
      intro u hu
      cases hu
    | tail _ h =>
      cases h with
      | head _ =>
        -- r = republicanRule; concl = "nonpacifist" ≠ "pacifist"
        decide
      | tail _ h' => cases h'

/-- **Rung 1 does NOT conclude `nonpacifist`**: symmetrically,
    republicanDefeater fires on `pacifist ∈ ReflConclAt T 0`. -/
theorem rung1_no_nonpacifist :
    ¬ Tower.ReflConclAt nixonTower 1 "nonpacifist" := by
  intro hc
  rw [Tower.reflConclAt_eq] at hc
  suffices h : ∀ a,
      Closure nixonTower.rules (Tower.isUndefeatedRefl nixonTower 1)
        (Tower.factsUpTo nixonTower 1) a → a ≠ "nonpacifist" by
    exact h "nonpacifist" hc rfl
  intro a hca
  induction hca with
  | fact hmem =>
    intro hEq
    subst hEq
    rw [nixon_factsUpTo_eq] at hmem
    exact absurd hmem (by decide)
  | rule r hr hact _hp _ih =>
    cases hr with
    | head _ =>
      decide
    | tail _ h =>
      cases h with
      | head _ =>
        intro _hEq
        apply hact republicanDefeater
          (by rw [nixon_defsUpTo_eq]; exact List.Mem.tail _ (List.Mem.head _))
          rfl
        refine ⟨rung0_concludes_pacifist, ?_⟩
        intro u hu
        cases hu
      | tail _ h' => cases h'

/-- **Skeptical rung.** At rung 1 — the rung where reflective
    defeating has fired — neither pacifist nor nonpacifist is
    concluded. This is the *skeptical reading* of Nixon Diamond. -/
theorem nixon_skeptical_at_rung1 :
    ¬ Tower.ReflConclAt nixonTower 1 "pacifist" ∧
    ¬ Tower.ReflConclAt nixonTower 1 "nonpacifist" :=
  ⟨rung1_no_pacifist, rung1_no_nonpacifist⟩

/-- **Credulous rung.** At rung 0 — the rung before reflective
    defeating fires — both pacifist and nonpacifist are concluded.
    This is the *credulous reading*: every consistent extension is
    available, but no choice is forced. -/
theorem nixon_credulous_at_rung0 :
    Tower.ReflConclAt nixonTower 0 "pacifist" ∧
    Tower.ReflConclAt nixonTower 0 "nonpacifist" :=
  ⟨rung0_concludes_pacifist, rung0_concludes_nonpacifist⟩

/-- **Nixon Diamond doesn't converge.** The conclusion sequence
    oscillates between the credulous and skeptical readings — at
    even rungs both are concluded, at odd rungs neither is. The
    framework's refusal to choose is structural, not accidental. -/
theorem nixon_diamond_irresolution :
    (Tower.ReflConclAt nixonTower 0 "pacifist" ∧
     Tower.ReflConclAt nixonTower 0 "nonpacifist") ∧
    (¬ Tower.ReflConclAt nixonTower 1 "pacifist" ∧
     ¬ Tower.ReflConclAt nixonTower 1 "nonpacifist") :=
  ⟨nixon_credulous_at_rung0, nixon_skeptical_at_rung1⟩

end Nixon
end Defeater
