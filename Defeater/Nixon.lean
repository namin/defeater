import Defeater.Reflection

/-
  Defeater/Nixon.lean — the Nixon Diamond.

  The textbook example of *symmetric defeasible conflict* (Reiter,
  McCarthy, ubiquitous since the 1980s):

    Quaker     ⇒ pacifist
    Republican ⇒ nonpacifist
    Nixon is both Quaker and Republican.

  Standard defeasible-logic readings of this scenario:
  - *Skeptical*: conclude neither — the conflicting defaults block
    each other.
  - *Credulous*: there are two consistent extensions, one with
    pacifist, one with nonpacifist.
  - *Specificity-based*: if no priority order is given, neither wins.

  Our minimal substrate has no priorities, no negation, and no
  formal extension semantics. We don't claim to instantiate the
  skeptical or credulous readings literally; we model the conflict
  via two rules and two rebutting defeaters (each rule's
  conclusion is the other defeater's trigger), and the reflective
  conclusion sequence oscillates with period 2:

    rung 0:  both concluded (pre-defeat baseline)
    rung 1:  neither concluded (post-defeat — each defeater fires
             reflectively on the other rule's rung-0 conclusion)
    rung 2:  both concluded again (rung-1's emptiness leaves both
             rules undefeated)
    ...

  The framework's refusal to converge is what's textbook-recognizable
  about Nixon Diamond — defeasible logic has no preferred answer
  here. The parity theorem `nixon_parity` makes this period-2
  oscillation a `∀ k` statement.
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

/-- **Post-defeat rung.** At rung 1 — the first rung where
    reflective defeating fires — neither pacifist nor nonpacifist
    is concluded; both rules have been mutually defeated.

    Note: this is *not* the formal "skeptical extension" of
    defeasible logic (which we don't have, lacking extension
    semantics). It's the rung-1 conclusion set under our reflective
    firing rule, which happens to coincide rhetorically with the
    skeptical reading. -/
theorem nixon_post_defeat_at_rung1 :
    ¬ Tower.ReflConclAt nixonTower 1 "pacifist" ∧
    ¬ Tower.ReflConclAt nixonTower 1 "nonpacifist" :=
  ⟨rung1_no_pacifist, rung1_no_nonpacifist⟩

/-- **Pre-defeat baseline.** At rung 0 — before any reflective
    defeating has fired — both pacifist and nonpacifist are
    concluded; both defaults fire from the asserted facts.

    Note: this is *not* the formal "credulous extension" — our
    substrate has no object-level negation, so concluding both
    `pacifist` and `nonpacifist` here is the both-defaults
    baseline, not a choice between two consistent extensions. -/
theorem nixon_baseline_at_rung0 :
    Tower.ReflConclAt nixonTower 0 "pacifist" ∧
    Tower.ReflConclAt nixonTower 0 "nonpacifist" :=
  ⟨rung0_concludes_pacifist, rung0_concludes_nonpacifist⟩

/-- **Nixon Diamond doesn't converge.** Three rungs witnessed: at
    rung 0 both are concluded, at rung 1 neither — and below we
    extend this to a ∀-theorem over all parities. -/
theorem nixon_diamond_irresolution :
    (Tower.ReflConclAt nixonTower 0 "pacifist" ∧
     Tower.ReflConclAt nixonTower 0 "nonpacifist") ∧
    (¬ Tower.ReflConclAt nixonTower 1 "pacifist" ∧
     ¬ Tower.ReflConclAt nixonTower 1 "nonpacifist") :=
  ⟨nixon_baseline_at_rung0, nixon_post_defeat_at_rung1⟩

/-! ## Period-2 forever, by induction

  Step lemmas generalize the rung-0 and rung-1 theorems above to
  arbitrary rungs; the parity theorem packages them as ∀ k.
-/

theorem any_concludes_quaker_cl (n : Nat) :
    Closure nixonTower.rules (Tower.isUndefeatedRefl nixonTower n)
      (Tower.factsUpTo nixonTower n) "quaker" := by
  apply Closure.fact
  rw [nixon_factsUpTo_eq]
  exact List.Mem.head _

theorem any_concludes_republican_cl (n : Nat) :
    Closure nixonTower.rules (Tower.isUndefeatedRefl nixonTower n)
      (Tower.factsUpTo nixonTower n) "republican" := by
  apply Closure.fact
  rw [nixon_factsUpTo_eq]
  exact List.Mem.tail _ (List.Mem.head _)

/-- Step down for `pacifist`: when `nonpacifist` was concluded at
    rung n, the quaker-overriding defeater fires at rung n+1. -/
theorem nixon_step_down_pacifist (n : Nat)
    (hN : Tower.ReflConclAt nixonTower n "nonpacifist") :
    ¬ Tower.ReflConclAt nixonTower (n + 1) "pacifist" := by
  intro hc
  rw [Tower.reflConclAt_eq] at hc
  suffices h : ∀ a,
      Closure nixonTower.rules (Tower.isUndefeatedRefl nixonTower (n + 1))
        (Tower.factsUpTo nixonTower (n + 1)) a → a ≠ "pacifist" by
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
      intro _hEq
      apply hact quakerDefeater
        (by rw [nixon_defsUpTo_eq]; exact List.Mem.head _)
        rfl
      refine ⟨hN, ?_⟩
      intro u hu; cases hu
    | tail _ h =>
      cases h with
      | head _ => decide
      | tail _ h' => cases h'

/-- Step down for `nonpacifist`: symmetric. -/
theorem nixon_step_down_nonpacifist (n : Nat)
    (hP : Tower.ReflConclAt nixonTower n "pacifist") :
    ¬ Tower.ReflConclAt nixonTower (n + 1) "nonpacifist" := by
  intro hc
  rw [Tower.reflConclAt_eq] at hc
  suffices h : ∀ a,
      Closure nixonTower.rules (Tower.isUndefeatedRefl nixonTower (n + 1))
        (Tower.factsUpTo nixonTower (n + 1)) a → a ≠ "nonpacifist" by
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
    | head _ => decide
    | tail _ h =>
      cases h with
      | head _ =>
        intro _hEq
        apply hact republicanDefeater
          (by rw [nixon_defsUpTo_eq]; exact List.Mem.tail _ (List.Mem.head _))
          rfl
        refine ⟨hP, ?_⟩
        intro u hu; cases hu
      | tail _ h' => cases h'

/-- Step up for `pacifist`: when `nonpacifist` was NOT concluded at
    rung n, the quaker-overriding defeater doesn't fire at rung n+1
    and the rule is undefeated. -/
theorem nixon_step_up_pacifist (n : Nat)
    (hNotN : ¬ Tower.ReflConclAt nixonTower n "nonpacifist") :
    Tower.ReflConclAt nixonTower (n + 1) "pacifist" := by
  rw [Tower.reflConclAt_eq]
  apply Closure.rule quakerRule
  · show quakerRule ∈ [quakerRule, republicanRule]
    exact List.Mem.head _
  · intro d hd hdr
    rw [nixon_defsUpTo_eq] at hd
    cases hd with
    | head _ =>
      intro ⟨hN, _⟩
      exact hNotN hN
    | tail _ h =>
      cases h with
      | head _ => exact absurd hdr (by decide)
      | tail _ h' => cases h'
  · intro p hp
    cases hp with
    | head _ => exact any_concludes_quaker_cl (n + 1)
    | tail _ h => cases h

/-- Step up for `nonpacifist`: symmetric. -/
theorem nixon_step_up_nonpacifist (n : Nat)
    (hNotP : ¬ Tower.ReflConclAt nixonTower n "pacifist") :
    Tower.ReflConclAt nixonTower (n + 1) "nonpacifist" := by
  rw [Tower.reflConclAt_eq]
  apply Closure.rule republicanRule
  · show republicanRule ∈ [quakerRule, republicanRule]
    exact List.Mem.tail _ (List.Mem.head _)
  · intro d hd hdr
    rw [nixon_defsUpTo_eq] at hd
    cases hd with
    | head _ => exact absurd hdr (by decide)
    | tail _ h =>
      cases h with
      | head _ =>
        intro ⟨hP, _⟩
        exact hNotP hP
      | tail _ h' => cases h'
  · intro p hp
    cases hp with
    | head _ => exact any_concludes_republican_cl (n + 1)
    | tail _ h => cases h

/-- **Period-2 parity, every rung.** For every `k`, both pacifist
    and nonpacifist are concluded at rung `2k`, and neither is
    concluded at rung `2k+1`. The conclusion sequence really does
    oscillate forever — Nixon Diamond's irresolution is structural,
    not just visible in the first few rungs. -/
theorem nixon_parity : ∀ k,
    (Tower.ReflConclAt nixonTower (2 * k) "pacifist" ∧
     Tower.ReflConclAt nixonTower (2 * k) "nonpacifist") ∧
    (¬ Tower.ReflConclAt nixonTower (2 * k + 1) "pacifist" ∧
     ¬ Tower.ReflConclAt nixonTower (2 * k + 1) "nonpacifist") := by
  intro k
  induction k with
  | zero => exact ⟨nixon_baseline_at_rung0, nixon_post_defeat_at_rung1⟩
  | succ m ih =>
    have h_up_p : Tower.ReflConclAt nixonTower (2 * (m + 1)) "pacifist" := by
      have heq : 2 * (m + 1) = 2 * m + 1 + 1 := by omega
      rw [heq]; exact nixon_step_up_pacifist _ ih.2.2
    have h_up_n : Tower.ReflConclAt nixonTower (2 * (m + 1)) "nonpacifist" := by
      have heq : 2 * (m + 1) = 2 * m + 1 + 1 := by omega
      rw [heq]; exact nixon_step_up_nonpacifist _ ih.2.1
    have h_down_p : ¬ Tower.ReflConclAt nixonTower (2 * (m + 1) + 1) "pacifist" :=
      nixon_step_down_pacifist _ h_up_n
    have h_down_n : ¬ Tower.ReflConclAt nixonTower (2 * (m + 1) + 1) "nonpacifist" :=
      nixon_step_down_nonpacifist _ h_up_p
    exact ⟨⟨h_up_p, h_up_n⟩, ⟨h_down_p, h_down_n⟩⟩

end Nixon
end Defeater
