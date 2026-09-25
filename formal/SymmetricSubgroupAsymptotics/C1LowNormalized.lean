import SymmetricSubgroupAsymptotics.C1LowCone
import SymmetricSubgroupAsymptotics.FusionArbitraryWidth

/-! The low one-triple cone is an actual forward row with an original
normalizer divisor six and a proved exponential decay in both parities. -/
set_option autoImplicit false
noncomputable section
open Filter
namespace SymmetricSubgroupAsymptotics

def c1LowKernel (m : ℕ) : ℝ := fusionWidthColdKernel m 3 1 6 ((6:ℝ)/25)

theorem c1LowKernel_nonneg (m : ℕ) : 0≤c1LowKernel m :=
  fusionWidthColdKernel_nonneg m 3 (by norm_num) (by norm_num)

theorem c1LowKernel_eventually : ∃ C : ℝ, 0<C ∧ ∀ᶠ m : ℕ in atTop,
    c1LowKernel m ≤ C*(2:ℝ)^(-(1/200:ℝ)*m) := by
  simpa only [c1LowKernel,halfDegree,show (3:ℕ)/2=1 by decide,Nat.cast_one,
    show ((1:ℝ)/4-6/25)/2=1/200 by norm_num] using
    fusionWidthColdKernel_eventually 3 (D := 1) (a := 6) (α := (6:ℝ)/25)
      (by norm_num) (by norm_num) (by norm_num [halfDegree])

/-- The exact complete lower-degree subgroup count appears only after
the surviving oriented character fibres have been bounded individually. -/
theorem c1Low_physical_normalized (m : ℕ)
    (P : Subgroup (TernaryCyclic × Equiv.Perm (Fin m)) → Prop)
    (hP : FusionOrbitNatural ternaryRegularAction
      (TernaryPhysicalPredicate (C1LowGraphPredicate m P))) :
    (Nat.card (FusionOrbitFamily ternaryRegularAction
      (TernaryPhysicalPredicate (C1LowGraphPredicate m P))):ℝ) / exactBenchmark (m+3) ≤
        c1LowKernel m * ((subgroupCount m:ℝ)/exactBenchmark m) := by
  have hL := exactBenchmark_pos m
  have hN := exactBenchmark_pos (m+3)
  have h := div_le_div_of_nonneg_right (c1Low_physical_card_le m P hP) hN.le
  apply h.trans_eq
  unfold c1LowKernel fusionWidthColdKernel fusionWidthPointingRatio
  field_simp

end SymmetricSubgroupAsymptotics
