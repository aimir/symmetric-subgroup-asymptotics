import SymmetricSubgroupAsymptotics.CFSGSymplecticElementaryCenter
import SymmetricSubgroupAsymptotics.CFSGSymplecticRootDiagonal
import SymmetricSubgroupAsymptotics.CFSGMatrixUnipotentScalar
import Mathlib.GroupTheory.QuotientGroup.Basic
import Mathlib.Tactic.Group

/-! The actual central quotient of the literal elementary symplectic
root group is centre-free. A projective scalar ambiguity on a unipotent
root is killed by the square-zero shifted matrix identity, not by an
order formula or a characteristic restriction. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGSymplecticSerreMatrices

abbrev elementaryProjective (K : Type*) [Field K] (r : ℕ) :=
  elementaryRootGroup K r ⧸ Subgroup.center (elementaryRootGroup K r)

theorem projective_central_lift_mem_center (K : Type*) [Field K] (r : ℕ)
    (u : elementaryRootGroup K (r + 1))
    (hu : (QuotientGroup.mk' (Subgroup.center (elementaryRootGroup K (r + 1)))) u ∈
      Subgroup.center (elementaryProjective K (r + 1))) :
    u ∈ Subgroup.center (elementaryRootGroup K (r + 1)) := by
  let q := QuotientGroup.mk' (Subgroup.center (elementaryRootGroup K (r + 1)))
  apply (elementaryRootGroup_center_iff_scalar K r u).mpr
  have hroot : ∀ neg i,
      (u.val : Mat K (r + 1)) * rootMatrix K (r + 1) neg i =
        rootMatrix K (r + 1) neg i * (u.val : Mat K (r + 1)) := by
    intro neg i
    let v : elementaryRootGroup K (r + 1) :=
      ⟨rootTransvection K (r + 1) neg i 1, rootTransvection_mem K (r + 1) neg i 1⟩
    have hcomm : q v * q u = q u * q v := (Subgroup.mem_center_iff.mp hu) (q v)
    have hk : q (u * v * u⁻¹ * v⁻¹) = 1 := by
      simp only [map_mul, map_inv]
      rw [← hcomm]
      group
    have hz : u * v * u⁻¹ * v⁻¹ ∈
        Subgroup.center (elementaryRootGroup K (r + 1)) :=
      (QuotientGroup.eq_one_iff _).mp hk
    obtain ⟨c, hc⟩ := (elementaryRootGroup_center_iff_scalar K r
      (u * v * u⁻¹ * v⁻¹)).mp hz
    have hm := congrArg (fun M : Mat K (r + 1) => M * (v.val : Mat K (r + 1))) hc
    change ((u.val : Mat K (r + 1)) * (v.val : Mat K (r + 1)) *
        (↑(u.val⁻¹) : Mat K (r + 1)) * (↑(v.val⁻¹) : Mat K (r + 1))) *
        (v.val : Mat K (r + 1)) = (c • (1 : Mat K (r + 1))) * (v.val : Mat K (r + 1)) at hm
    simp only [mul_assoc, Units.inv_mul, mul_one, smul_mul_assoc, one_mul] at hm
    have hconj : (u.val : Mat K (r + 1)) * (1 + (1 : K) • rootMatrix K (r + 1) neg i) *
        (↑(u.val⁻¹) : Mat K (r + 1)) =
        c • (1 + (1 : K) • rootMatrix K (r + 1) neg i) := by
      simpa only [v, rootTransvection_val, mul_assoc] using hm
    have hc1 : c = 1 := CFSGMatrixUnipotentScalar.scalar_conjugate_transvection
      (rootMatrix K (r + 1) neg i) (rootMatrix_sq_zero K (r + 1) neg i)
      (Sum.inl (Fin.last r)) (rootMatrix_diagonal K (r + 1) neg i _)
      u.val (1 : K) c hconj
    simp only [hc1, one_smul] at hconj
    have h := (unit_conjugation_fix_iff_commute u.val _).mp hconj
    simp only [mul_add, add_mul, mul_one, one_mul] at h
    exact add_left_cancel h
  exact simple_root_centralizer r (u.val : Mat K (r + 1)) (hroot false) (hroot true)

theorem elementaryProjective_center_eq_bot (K : Type*) [Field K] (r : ℕ) :
    Subgroup.center (elementaryProjective K (r + 1)) = ⊥ := by
  apply bot_unique
  intro z hz
  obtain ⟨u, rfl⟩ := (QuotientGroup.mk'_surjective
    (Subgroup.center (elementaryRootGroup K (r + 1)))) z
  change (QuotientGroup.mk' (Subgroup.center (elementaryRootGroup K (r + 1)))) u = 1
  exact (QuotientGroup.eq_one_iff u).mpr
    (projective_central_lift_mem_center K r u hz)

end SymmetricSubgroupAsymptotics.CFSGSymplecticSerreMatrices
