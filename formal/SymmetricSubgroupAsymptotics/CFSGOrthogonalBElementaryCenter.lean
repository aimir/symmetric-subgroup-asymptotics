import SymmetricSubgroupAsymptotics.CFSGOrthogonalBRootCentralizer
import SymmetricSubgroupAsymptotics.CFSGOrthogonalBElementaryGroup
import SymmetricSubgroupAsymptotics.CFSGQuadraticRootCentralizer

/-! The actual type-B elementary matrix centre is scalar in odd
characteristic. Recovery of the genuine linear root retains the
quadratic coefficient and explicitly cancels two. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGOrthogonalBSerreMatrices

theorem elementaryRootGroup_center_iff_scalar (K : Type*) [Field K] (r : ℕ)
    (h2 : (2 : K) ≠ 0) (u : elementaryRootGroup K (r + 1)) :
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
      change (u.val : Mat K (r + 1)) *
          (1 + (1 : K) • rootMatrix K (r + 1) neg i +
            (1 : K)^2 • rootSecond K (r + 1) neg i) =
        (1 + (1 : K) • rootMatrix K (r + 1) neg i +
          (1 : K)^2 • rootSecond K (r + 1) neg i) * (u.val : Mat K (r + 1)) at h
      simp only [one_pow, one_smul] at h
      exact CFSGQuadraticRootCentralizer.commutes_linear_of_commutes_quadratic h2
        (u.val : Mat K (r + 1)) _ _
        (rootMatrix_square K (r + 1) neg i) (rootMatrix_mul_second K (r + 1) neg i)
        (rootSecond_mul_matrix K (r + 1) neg i) (rootSecond_square K (r + 1) neg i) h
    exact simple_root_centralizer r h2 (u.val : Mat K (r + 1)) (hroot false) (hroot true)
  · rintro ⟨c, hc⟩
    apply Subgroup.mem_center_iff.mpr
    intro v
    apply Subtype.ext
    apply Units.ext
    change (v.val : Mat K (r + 1)) * (u.val : Mat K (r + 1)) =
      (u.val : Mat K (r + 1)) * (v.val : Mat K (r + 1))
    rw [hc]
    simp only [mul_smul_comm, smul_mul_assoc, mul_one, one_mul]

end SymmetricSubgroupAsymptotics.CFSGOrthogonalBSerreMatrices
