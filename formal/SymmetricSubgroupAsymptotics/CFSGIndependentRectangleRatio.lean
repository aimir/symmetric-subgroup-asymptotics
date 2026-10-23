import SymmetricSubgroupAsymptotics.CFSGIndependentPairRayRatio

/-! Two independent component comparisons force the same mixed-ray
ratio on the two ends of an isotropic rectangle. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section

namespace SymmetricSubgroupAsymptotics.CFSGIndependentRectangleRatio
variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]

theorem ratio_eq_of_two_component_comparisons (x₁ x₂ y₁ y₂ : V)
    (hx : LinearIndependent K ![x₁, x₂]) (hy : LinearIndependent K ![y₁, y₂])
    (a b c d t u : K) (ha : a ≠ 0)
    (hP : a • x₁ + b • x₂ = c • (x₁ + x₂))
    (hZ : (a * t) • y₁ + (b * u) • y₂ = d • (y₁ + y₂)) : t = u := by
  have hxp : (a - c) • x₁ + (b - c) • x₂ = 0 := by
    calc
      _ = (a • x₁ + b • x₂) - c • (x₁ + x₂) := by module
      _ = 0 := sub_eq_zero.mpr hP
  obtain ⟨hac, hbc⟩ := LinearIndependent.pair_iff.mp hx (a - c) (b - c) hxp
  have hab : a = b := (sub_eq_zero.mp hac).trans (sub_eq_zero.mp hbc).symm
  have hyp : (a * t - d) • y₁ + (b * u - d) • y₂ = 0 := by
    calc
      _ = ((a * t) • y₁ + (b * u) • y₂) - d • (y₁ + y₂) := by module
      _ = 0 := sub_eq_zero.mpr hZ
  obtain ⟨hat, hbu⟩ := LinearIndependent.pair_iff.mp hy (a * t - d) (b * u - d) hyp
  apply mul_left_cancel₀ ha
  calc
    a * t = d := sub_eq_zero.mp hat
    _ = b * u := (sub_eq_zero.mp hbu).symm
    _ = a * u := congrArg (fun z : K => z * u) hab.symm

end SymmetricSubgroupAsymptotics.CFSGIndependentRectangleRatio
