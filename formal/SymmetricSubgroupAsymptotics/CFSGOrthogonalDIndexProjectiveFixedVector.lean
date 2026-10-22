import SymmetricSubgroupAsymptotics.CFSGOrthogonalDIndexProjectiveUnipotent

/-! Equal original projective representatives with a common nonzero
fixed vector are equal whenever their quotient is an actual scalar.
Here scalar recognition is the checked literal D-centre theorem. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Matrix
namespace SymmetricSubgroupAsymptotics.CFSGOrthogonalDIndexProjectiveFixedVector
open CFSGOrthogonalDSerreMatrices CFSGOrthogonalDIndexProjectiveUnipotent
variable (K : Type) [Field K]

theorem eq_of_projective_eq_of_joint_fixed (s : ℕ)
    (u v : elementaryRootGroup K (s + 4))
    (he : projection K s u = projection K s v)
    (x : Index (s + 4) → K) (hx : x ≠ 0)
    (hu : (u.val : Mat K (s + 4)) *ᵥ x = x)
    (hv : (v.val : Mat K (s + 4)) *ᵥ x = x) : u = v := by
  have hc : u / v ∈ Subgroup.center (elementaryRootGroup K (s + 4)) :=
    QuotientGroup.eq_iff_div_mem.mp he
  obtain ⟨a, ha⟩ := (elementaryRootGroup_center_iff_scalar K (s + 2) (u / v)).mp hc
  have hm := congrArg (fun z : elementaryRootGroup K (s + 4) => (z.val : Mat K (s + 4)))
    (div_mul_cancel u v).symm
  change (u.val : Mat K (s + 4)) = ((u / v).val : Mat K (s + 4)) *
    (v.val : Mat K (s + 4)) at hm
  rw [ha] at hm
  have hax : x = a • x := by
    calc
      x = (u.val : Mat K (s + 4)) *ᵥ x := hu.symm
      _ = ((a • (1 : Mat K (s + 4))) * (v.val : Mat K (s + 4))) *ᵥ x := by rw [hm]
      _ = a • x := by
        rw [← Matrix.mulVec_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec, hv]
  have ha1 : a = 1 := smul_left_injective K hx (by simpa only [one_smul] using hax.symm)
  apply Subtype.ext
  apply Units.ext
  simpa only [ha1, one_smul, one_mul] using hm

end SymmetricSubgroupAsymptotics.CFSGOrthogonalDIndexProjectiveFixedVector
