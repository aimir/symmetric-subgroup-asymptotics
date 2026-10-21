import SymmetricSubgroupAsymptotics.CFSGOrthogonalDElementaryGroup
import SymmetricSubgroupAsymptotics.CFSGOrthogonalDRootCentralizer
import Mathlib.GroupTheory.Subgroup.Center

/-! The actual centre of the literal D elementary root group consists
exactly of scalar matrices, by the proved original-root commutant. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGOrthogonalDSerreMatrices

theorem elementaryRootGroup_center_iff_scalar (K : Type*) [CommRing K] (r : ℕ)
    (u : elementaryRootGroup K (r+2)) :
    u∈Subgroup.center (elementaryRootGroup K (r+2))↔
      ∃c : K,(u.val : Mat K (r+2))=c • (1 : Mat K (r+2)) := by
  constructor
  · intro hu
    have hroot : ∀neg i,(u.val : Mat K (r+2))*rootMatrix K (r+2) neg i=
        rootMatrix K (r+2) neg i*(u.val : Mat K (r+2)) := by
      intro neg i
      let v : elementaryRootGroup K (r+2) :=
        ⟨rootTransvection K (r+2) neg i 1,rootTransvection_mem K (r+2) neg i 1⟩
      have hh := congrArg (fun w : elementaryRootGroup K (r+2) => (w.val : Mat K (r+2)))
        ((Subgroup.mem_center_iff.mp hu) v).symm
      change (u.val : Mat K (r+2))*(1+1 • rootMatrix K (r+2) neg i)=
        (1+1 • rootMatrix K (r+2) neg i)*(u.val : Mat K (r+2)) at hh
      simp only [one_smul,mul_add,add_mul,mul_one,one_mul] at hh
      exact add_left_cancel hh
    exact simple_root_centralizer r (u.val : Mat K (r+2)) (hroot false) (hroot true)
  · rintro ⟨c,hc⟩
    apply Subgroup.mem_center_iff.mpr
    intro v
    apply Subtype.ext
    apply Units.ext
    change (v.val : Mat K (r+2))*(u.val : Mat K (r+2))=
      (u.val : Mat K (r+2))*(v.val : Mat K (r+2))
    rw [hc]
    simp only [mul_smul_comm,smul_mul_assoc,mul_one,one_mul]

end SymmetricSubgroupAsymptotics.CFSGOrthogonalDSerreMatrices
