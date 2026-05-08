import Defeater.Tower

/-
  Defeater/Trust.lean — a trust hierarchy / source-credibility
  cascade.

  The rung index here is *not* admission order — it is an
  authority lattice. Rung n+1 is strictly more authoritative than
  rung n; admitting a defeater at rung n+1 means "a higher-ranked
  source has spoken, defeating a lower-ranked source's default."

  Scenario: three sources of testimony about a suspect's coat color.
    rung 0: a junior witness reports `juniorTestimony`.
            Default rule: junior testimony ⇒ redCoat.
            Conclusion: redCoat.
    rung 1: a senior witness reports `seniorTestimony`.
            Senior outranks junior — admit a defeater of the
            junior's rule, triggered by senior testimony.
            Senior's own rule: senior testimony ⇒ blueCoat.
            Conclusion: blueCoat (junior's claim defeated).
    rung 2: forensic evidence `forensicReport` arrives.
            Forensic outranks senior — admit a defeater of the
            senior's rule, triggered by forensic.
            Forensic's own rule: forensic ⇒ greenCoat.
            Conclusion: greenCoat (senior's claim defeated).

  As the agent ascends the trust hierarchy, the conclusion shifts
  to reflect the most authoritative source. The rung structure is
  literally the authority order — the keynote's reflective tower
  given concrete epistemic content.
-/

namespace Defeater
namespace Trust

/-- Standard env: in the actual world, the coat is green (matching
    the highest-authority source). Junior's and senior's claims are
    false; forensic's claim is true. -/
def trustEnv : Env := fun a =>
  match a with
  | "juniorTestimony" => True
  | "seniorTestimony" => True
  | "forensicReport"  => True
  | "redCoat"         => False
  | "blueCoat"        => False
  | "greenCoat"       => True
  | _                 => False

def juniorRule : DefRule :=
  { prems := ["juniorTestimony"], concl := "redCoat" }

def seniorRule : DefRule :=
  { prems := ["seniorTestimony"], concl := "blueCoat" }

def forensicRule : DefRule :=
  { prems := ["forensicReport"], concl := "greenCoat" }

/-- Senior outranks junior: when the senior has testified, the
    junior's default is defeated. -/
def seniorOverridesJunior : SoundDefeater trustEnv where
  rule := juniorRule
  trigger := "seniorTestimony"
  undercutters := []
  defeats := by
    intro _ _ hredCoat
    exact hredCoat

/-- Forensic outranks senior: when forensic has reported, the
    senior's default is defeated. -/
def forensicOverridesSenior : SoundDefeater trustEnv where
  rule := seniorRule
  trigger := "forensicReport"
  undercutters := []
  defeats := by
    intro _ _ hblueCoat
    exact hblueCoat

/-- The trust-hierarchy tower. Each rung admits a more authoritative
    source: junior at rung 0, senior at rung 1 (with override of
    junior), forensic at rung 2 (with override of senior). -/
def trustTower : Tower trustEnv where
  rules := [juniorRule, seniorRule, forensicRule]
  facts := fun n => match n with
    | 0 => ["juniorTestimony"]
    | 1 => ["seniorTestimony"]
    | 2 => ["forensicReport"]
    | _ => []
  defs := fun n => match n with
    | 1 => [seniorOverridesJunior]
    | 2 => [forensicOverridesSenior]
    | _ => []

theorem trust_factsUpTo_0 :
    Tower.factsUpTo trustTower 0 = ["juniorTestimony"] := rfl

theorem trust_factsUpTo_1 :
    Tower.factsUpTo trustTower 1 = ["juniorTestimony", "seniorTestimony"] := rfl

theorem trust_factsUpTo_2 :
    Tower.factsUpTo trustTower 2 =
    ["juniorTestimony", "seniorTestimony", "forensicReport"] := rfl

theorem trust_defsUpTo_0 :
    Tower.defsUpTo trustTower 0 = [] := rfl

theorem trust_defsUpTo_1 :
    Tower.defsUpTo trustTower 1 = [seniorOverridesJunior] := rfl

theorem trust_defsUpTo_2 :
    Tower.defsUpTo trustTower 2 =
    [seniorOverridesJunior, forensicOverridesSenior] := rfl

/-- **Rung 0 concludes `redCoat`**: only the junior has testified;
    no defeaters yet; the junior's default fires. -/
theorem rung0_concludes_redCoat :
    Tower.ConclAt trustTower 0 "redCoat" := by
  apply Tower.ConclAt.rule juniorRule
  · show juniorRule ∈ [juniorRule, seniorRule, forensicRule]
    exact List.Mem.head _
  · intro d hd _
    rw [trust_defsUpTo_0] at hd
    cases hd
  · intro p hp
    apply Tower.ConclAt.fact
    rw [trust_factsUpTo_0]
    exact hp

/-- **Rung 1 concludes `blueCoat`**: senior has testified; senior's
    default fires; senior's rule is undefeated (no defeater targets
    it yet). -/
theorem rung1_concludes_blueCoat :
    Tower.ConclAt trustTower 1 "blueCoat" := by
  apply Tower.ConclAt.rule seniorRule
  · show seniorRule ∈ [juniorRule, seniorRule, forensicRule]
    exact List.Mem.tail _ (List.Mem.head _)
  · -- isUndefeated 1 seniorRule: at rung 1, only seniorOverridesJunior
    -- is admitted, and it targets juniorRule, not seniorRule.
    intro d hd hdr
    rw [trust_defsUpTo_1] at hd
    cases hd with
    | head _ =>
      -- d = seniorOverridesJunior; hdr : its rule = seniorRule
      -- but seniorOverridesJunior.rule = juniorRule
      exact absurd hdr (by decide)
    | tail _ h => cases h
  · intro p hp
    apply Tower.ConclAt.fact
    rw [trust_factsUpTo_1]
    cases hp with
    | head _ => exact List.Mem.tail _ (List.Mem.head _)
    | tail _ h => cases h

/-- **Rung 1 does NOT conclude `redCoat`**: junior's default has
    been defeated by the senior's testimony (the seniorOverrides-
    Junior defeater fires syntactically). -/
theorem rung1_no_redCoat :
    ¬ Tower.ConclAt trustTower 1 "redCoat" := by
  intro hc
  suffices h : ∀ a, Tower.ConclAt trustTower 1 a → a ≠ "redCoat" by
    exact h "redCoat" hc rfl
  intro a hca
  induction hca with
  | fact hmem =>
    intro hEq
    subst hEq
    rw [trust_factsUpTo_1] at hmem
    exact absurd hmem (by decide)
  | rule r hr hund _hp _ih =>
    cases hr with
    | head _ =>
      -- r = juniorRule; concl = "redCoat". The junior-overriding
      -- defeater fires at rung 1 (senior testimony asserted).
      intro _hEq
      apply hund seniorOverridesJunior
        (by rw [trust_defsUpTo_1]; exact List.Mem.head _)
        rfl
      refine ⟨?_, ?_⟩
      · -- "seniorTestimony" ∈ factsUpTo 1
        show "seniorTestimony" ∈ Tower.factsUpTo trustTower 1
        rw [trust_factsUpTo_1]; decide
      · intro u hu; cases hu
    | tail _ h =>
      cases h with
      | head _ =>
        -- r = seniorRule; concl = "blueCoat" ≠ "redCoat"
        decide
      | tail _ h' =>
        cases h' with
        | head _ =>
          -- r = forensicRule; concl = "greenCoat" ≠ "redCoat"
          decide
        | tail _ h'' => cases h''

/-- **Rung 2 concludes `greenCoat`**: forensic has reported;
    forensic's default fires; forensic's rule is undefeated (no
    defeater targets it). -/
theorem rung2_concludes_greenCoat :
    Tower.ConclAt trustTower 2 "greenCoat" := by
  apply Tower.ConclAt.rule forensicRule
  · show forensicRule ∈ [juniorRule, seniorRule, forensicRule]
    exact List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))
  · -- isUndefeated 2 forensicRule: no admitted defeater targets it.
    intro d hd hdr
    rw [trust_defsUpTo_2] at hd
    cases hd with
    | head _ =>
      -- d = seniorOverridesJunior; rule = juniorRule ≠ forensicRule
      exact absurd hdr (by decide)
    | tail _ h =>
      cases h with
      | head _ =>
        -- d = forensicOverridesSenior; rule = seniorRule ≠ forensicRule
        exact absurd hdr (by decide)
      | tail _ h' => cases h'
  · intro p hp
    apply Tower.ConclAt.fact
    rw [trust_factsUpTo_2]
    cases hp with
    | head _ =>
      -- p = "forensicReport"; in factsUpTo 2
      exact List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))
    | tail _ h => cases h

/-- **Rung 2 does NOT conclude `blueCoat`**: senior's default has
    been defeated by the forensic report. -/
theorem rung2_no_blueCoat :
    ¬ Tower.ConclAt trustTower 2 "blueCoat" := by
  intro hc
  suffices h : ∀ a, Tower.ConclAt trustTower 2 a → a ≠ "blueCoat" by
    exact h "blueCoat" hc rfl
  intro a hca
  induction hca with
  | fact hmem =>
    intro hEq
    subst hEq
    rw [trust_factsUpTo_2] at hmem
    exact absurd hmem (by decide)
  | rule r hr hund _hp _ih =>
    cases hr with
    | head _ =>
      -- r = juniorRule; concl = "redCoat" ≠ "blueCoat"
      decide
    | tail _ h =>
      cases h with
      | head _ =>
        -- r = seniorRule; concl = "blueCoat". forensicOverridesSenior fires.
        intro _hEq
        apply hund forensicOverridesSenior
          (by rw [trust_defsUpTo_2]; exact List.Mem.tail _ (List.Mem.head _))
          rfl
        refine ⟨?_, ?_⟩
        · show "forensicReport" ∈ Tower.factsUpTo trustTower 2
          rw [trust_factsUpTo_2]; decide
        · intro u hu; cases hu
      | tail _ h' =>
        cases h' with
        | head _ =>
          -- r = forensicRule; concl = "greenCoat" ≠ "blueCoat"
          decide
        | tail _ h'' => cases h''

/-- **Rung 2 still does NOT conclude `redCoat`**: the
    seniorOverridesJunior defeater is still admitted (defeaters,
    once admitted, remain in `defsUpTo`), and senior testimony is
    still asserted. -/
theorem rung2_no_redCoat :
    ¬ Tower.ConclAt trustTower 2 "redCoat" := by
  intro hc
  suffices h : ∀ a, Tower.ConclAt trustTower 2 a → a ≠ "redCoat" by
    exact h "redCoat" hc rfl
  intro a hca
  induction hca with
  | fact hmem =>
    intro hEq
    subst hEq
    rw [trust_factsUpTo_2] at hmem
    exact absurd hmem (by decide)
  | rule r hr hund _hp _ih =>
    cases hr with
    | head _ =>
      -- r = juniorRule; concl = "redCoat". seniorOverridesJunior fires.
      intro _hEq
      apply hund seniorOverridesJunior
        (by rw [trust_defsUpTo_2]; exact List.Mem.head _)
        rfl
      refine ⟨?_, ?_⟩
      · show "seniorTestimony" ∈ Tower.factsUpTo trustTower 2
        rw [trust_factsUpTo_2]; decide
      · intro u hu; cases hu
    | tail _ h =>
      cases h with
      | head _ =>
        decide
      | tail _ h' =>
        cases h' with
        | head _ => decide
        | tail _ h'' => cases h''

/-- **The trust-hierarchy summary.** The conclusion shifts as we
    ascend the authority lattice — at each rung, the most
    authoritative source's claim is what's concluded; lower-ranked
    sources' claims have been defeated.

    The rung index is doing real semantic work: rung n+1 is "more
    authoritative" than rung n, and admission at the higher rung
    means "this source outranks all below." -/
theorem trust_cascade :
    Tower.ConclAt trustTower 0 "redCoat" ∧
    (Tower.ConclAt trustTower 1 "blueCoat" ∧ ¬ Tower.ConclAt trustTower 1 "redCoat") ∧
    (Tower.ConclAt trustTower 2 "greenCoat" ∧
     ¬ Tower.ConclAt trustTower 2 "blueCoat" ∧
     ¬ Tower.ConclAt trustTower 2 "redCoat") :=
  ⟨rung0_concludes_redCoat,
   ⟨rung1_concludes_blueCoat, rung1_no_redCoat⟩,
   ⟨rung2_concludes_greenCoat, rung2_no_blueCoat, rung2_no_redCoat⟩⟩

end Trust
end Defeater
