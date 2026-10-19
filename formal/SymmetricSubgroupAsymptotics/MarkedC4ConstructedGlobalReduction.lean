import SymmetricSubgroupAsymptotics.MarkedC4ConstructedLargeOrbitCutoff

/-! Compose the constructed large-orbit theorem with a proved fixed-cutoff
bound. The fixed-cutoff bound is still explicit: this is a conditional
assembly theorem, not a claim that the sharp bounded-word work is complete.
Unlike the legacy RDT assembly, it takes no project-owned large-orbit
encoding constructor. -/
set_option autoImplicit false
noncomputable section
open Filter
namespace SymmetricSubgroupAsymptotics.MarkedC4.ConstructedGlobalReduction
open LargeOrbitOrdinaryGeneration SolubleContainerCount SolubleContainerOrder

theorem solubleGlobal_of_smallSource
    (h62 : PublishedProposition62) (h86 : PublishedTheorem86Representatives)
    (hDixon : PublishedDixonOrder)
    (hsmall : ∀ C : ℕ, 2 ≤ C → ∀ ε : ℝ, 0 < ε → ∀ K : ℝ,
      ∀ᶠ b : ℕ in atTop, ∀ r : ℕ, (r : ℝ) ≤ K*b →
        OrbitCutoffFamilies.solubleCount C b r ≤
          (2 : ℝ)^(markedF b r + ε*((b : ℝ)+r)^2)) :
    SolubleGlobalMarkedC4MomentBound := by
  intro ε hε K
  have hthird : 0 < ε/3 := by positivity
  obtain ⟨C,hC,hlarge⟩ := ConstructedLargeOrbitCutoff.marked_bound h62 h86 hDixon
    (ε/3) hthird
  filter_upwards [hlarge,hsmall C hC (ε/3) hthird K] with b hlargeb hsmallb
  intro r hr
  calc
    solubleMarkedC4Moment b r ≤
        (2 : ℝ)^((ε/3)*((b : ℝ)+r)^2) * OrbitCutoffFamilies.solubleCount C b r := hlargeb r
    _ ≤ (2 : ℝ)^((ε/3)*((b : ℝ)+r)^2) *
        (2 : ℝ)^(markedF b r + (ε/3)*((b : ℝ)+r)^2) :=
      mul_le_mul_of_nonneg_left (hsmallb r hr) (by positivity)
    _ ≤ (2 : ℝ)^(markedF b r + ε*((b : ℝ)+r)^2) := by
      rw [← Real.rpow_add (by norm_num : (0 : ℝ)<2)]
      apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
      nlinarith [sq_nonneg ((b : ℝ)+r)]

end SymmetricSubgroupAsymptotics.MarkedC4.ConstructedGlobalReduction
end
