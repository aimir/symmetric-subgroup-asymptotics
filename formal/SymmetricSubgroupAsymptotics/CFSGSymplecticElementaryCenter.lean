import SymmetricSubgroupAsymptotics.CFSGSymplecticElementaryGroup
import SymmetricSubgroupAsymptotics.CFSGSymplecticImageCentralizer
import Mathlib.GroupTheory.Subgroup.Center

/-! The literal elementary root-group centre is exactly its scalar
matrices. Its conjugation kernel on the SAME actual Serre image is that
centre, without a full classical Lie-image or group-order calculation. -/
set_option autoImplicit false
noncomputable section
open scoped TensorProduct
namespace SymmetricSubgroupAsymptotics.CFSGSymplecticSerreMatrices
open CFSG.Models.Chevalley

theorem elementaryRootGroup_center_iff_scalar (K : Type*) [CommRing K] (r : ℕ)
    (u : elementaryRootGroup K (r + 1)) :
    u ∈ Subgroup.center (elementaryRootGroup K (r + 1)) ↔
      ∃ c : K, (u.val : Mat K (r + 1)) = c • (1 : Mat K (r + 1)) := by
  constructor
  · intro hu
    have hroot : ∀ neg i,
        (u.val : Mat K (r + 1)) * rootMatrix K (r + 1) neg i =
          rootMatrix K (r + 1) neg i * (u.val : Mat K (r + 1)) := by
      intro neg i
      let v : elementaryRootGroup K (r + 1) :=
        ⟨rootTransvection K (r + 1) neg i 1, rootTransvection_mem K (r + 1) neg i 1⟩
      have h := congrArg (fun w : elementaryRootGroup K (r + 1) =>
        (w.val : Mat K (r + 1))) ((Subgroup.mem_center_iff.mp hu) v).symm
      change (u.val : Mat K (r + 1)) * (1 + 1 • rootMatrix K (r + 1) neg i) =
        (1 + 1 • rootMatrix K (r + 1) neg i) * (u.val : Mat K (r + 1)) at h
      simp only [one_smul, mul_add, add_mul, mul_one, one_mul] at h
      exact add_left_cancel h
    exact simple_root_centralizer r (u.val : Mat K (r + 1))
      (hroot false) (hroot true)
  · rintro ⟨c, hc⟩
    apply Subgroup.mem_center_iff.mpr
    intro v
    apply Subtype.ext
    apply Units.ext
    change (v.val : Mat K (r + 1)) * (u.val : Mat K (r + 1)) =
      (u.val : Mat K (r + 1)) * (v.val : Mat K (r + 1))
    rw [hc]
    simp only [mul_smul_comm, smul_mul_assoc, mul_one, one_mul]

theorem elementaryRootGroup_image_conjugation_kernel (K : Type*) [CommRing K] (r : ℕ)
    (u : elementaryRootGroup K (r + 1)) :
    (∀ x : K ⊗[ℤ] integralLattice (CartanMatrix.C (r + 1)).transpose,
      (u.val : Mat K (r + 1)) * symplecticBaseChange K (r + 1) x * (↑(u.val⁻¹) : Mat K (r + 1)) =
        symplecticBaseChange K (r + 1) x) ↔
      u ∈ Subgroup.center (elementaryRootGroup K (r + 1)) := by
  constructor
  · intro hu
    exact (elementaryRootGroup_center_iff_scalar K r u).mpr
      (symplecticImage_conjugation_kernel_scalar K r u.val hu)
  · intro hu x
    obtain ⟨c, hc⟩ := (elementaryRootGroup_center_iff_scalar K r u).mp hu
    apply (unit_conjugation_fix_iff_commute u.val _).mpr
    rw [hc]
    simp only [smul_mul_assoc, mul_smul_comm, one_mul, mul_one]

end SymmetricSubgroupAsymptotics.CFSGSymplecticSerreMatrices
