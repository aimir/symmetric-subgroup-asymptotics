import SymmetricSubgroupAsymptotics.CFSGOrthogonalDIntegralRealization
import SymmetricSubgroupAsymptotics.CFSGSerreSquareZeroMatrixActions
import SymmetricSubgroupAsymptotics.CFSGOrthogonalDElementaryCenter
import SymmetricSubgroupAsymptotics.CFSGUnitConjugation

/-! The original D model and literal natural root group act on the SAME
actual integral matrix image. Its action kernel is the actual centre. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped TensorProduct
namespace SymmetricSubgroupAsymptotics.CFSGOrthogonalDSerreMatrices
open CFSG.Models.Chevalley

theorem rootTransvection_val_data (K : Type) [Field K] (r : ℕ) (hr : 4≤r)
    (neg : Bool) (i : Fin r) (t : K) :
    (rootTransvection K r neg i t : Mat K r)=
      1+t • CFSGSerreSquareZeroMatrix.fieldRoot (realizationData r hr) K neg i := by
  rw [realizationData_fieldRoot]
  rfl

theorem rootTransvection_inv_val_data (K : Type) [Field K] (r : ℕ) (hr : 4≤r)
    (neg : Bool) (i : Fin r) (t : K) :
    (↑((rootTransvection K r neg i t)⁻¹) : Mat K r)=
      1-t • CFSGSerreSquareZeroMatrix.fieldRoot (realizationData r hr) K neg i := by
  rw [realizationData_fieldRoot]
  rfl

abbrev orthogonalImageRepresentation (K : Type) [Field K] (r : ℕ) (hr : 4≤r) :=
  CFSGSerreSquareZeroMatrix.imageRepresentation (realizationData r hr) K

abbrev elementaryImageAction (K : Type) [Field K] (r : ℕ) (hr : 4≤r) :=
  CFSGSerreSquareZeroMatrix.elementaryImageAction (realizationData r hr) K (rootTransvection K r)
    (rootTransvection_val_data K r hr) (rootTransvection_inv_val_data K r hr)

theorem orthogonal_action_ranges_eq (K : Type) [Field K] (r : ℕ) (hr : 4≤r) :
    (orthogonalImageRepresentation K r hr).range=(elementaryImageAction K r hr).range :=
  CFSGSerreSquareZeroMatrix.action_ranges_eq (realizationData r hr) K (rootTransvection K r)
    (rootTransvection_val_data K r hr) (rootTransvection_inv_val_data K r hr)

theorem orthogonalImage_centralizer (K : Type) [Field K] (r : ℕ) (A : Mat K (r+4))
    (hA : ∀x : Space (CartanMatrix.D (r+4)) K,
      A*orthogonalBaseChange K (r+4) (by omega) x=orthogonalBaseChange K (r+4) (by omega) x*A) :
    ∃c : K,A=c • (1 : Mat K (r+4)) := by
  apply simple_root_centralizer (r+2) A
  · intro i
    have hh := hA (1 ⊗ₜ[ℤ] CFSGSerreDiagram.latticeGenerator (CartanMatrix.D (r+4)) (CartanMatrix.Generators.E i))
    simpa only [orthogonalBaseChange_E] using hh
  · intro i
    have hh := hA (1 ⊗ₜ[ℤ] CFSGSerreDiagram.latticeGenerator (CartanMatrix.D (r+4)) (CartanMatrix.Generators.F i))
    simpa only [orthogonalBaseChange_F] using hh

theorem elementaryImageAction_ker (K : Type) [Field K] (r : ℕ) :
    (elementaryImageAction K (r+4) (by omega)).ker=Subgroup.center (elementaryRootGroup K (r+4)) := by
  have hr : 4 ≤ r+4 := by omega
  ext u
  change elementaryImageAction K (r+4) hr u=1↔u∈Subgroup.center (elementaryRootGroup K (r+4))
  constructor
  · intro hu
    apply (elementaryRootGroup_center_iff_scalar K (r+2) u).mpr
    apply orthogonalImage_centralizer K r (u.val : Mat K (r+4))
    intro x
    have hh := DFunLike.congr_fun hu ((orthogonalBaseChange K (r+4) hr).rangeRestrict x)
    have he := congrArg Subtype.val hh
    change (u.val : Mat K (r+4))*orthogonalBaseChange K (r+4) hr x*
      (↑(u.val⁻¹):Mat K (r+4))=orthogonalBaseChange K (r+4) hr x at he
    exact (CFSGUnitConjugation.fix_iff_commute u.val _).mp he
  · intro hu
    obtain ⟨c,hc⟩ := (elementaryRootGroup_center_iff_scalar K (r+2) u).mp hu
    apply LinearEquiv.ext
    intro y
    apply Subtype.ext
    change (u.val : Mat K (r+4))*y.val*(↑(u.val⁻¹):Mat K (r+4))=y.val
    apply (CFSGUnitConjugation.fix_iff_commute u.val _).mpr
    rw [hc]
    simp only [smul_mul_assoc,mul_smul_comm,one_mul,mul_one]

def elementaryProjectiveActionEquiv (K : Type) [Field K] (r : ℕ) :
    elementaryProjective K (r+4)≃*(elementaryImageAction K (r+4) (by omega)).range := by
  have hr : 4 ≤ r+4 := by omega
  let f : elementaryRootGroup K (r+4) →*
      ((orthogonalBaseChange K (r+4) hr).range ≃ₗ[K]
        (orthogonalBaseChange K (r+4) hr).range) := elementaryImageAction K (r+4) hr
  have hf : f.ker=Subgroup.center (elementaryRootGroup K (r+4)) :=
    elementaryImageAction_ker K r
  letI : f.ker.Normal := f.normal_ker
  letI : Group (elementaryRootGroup K (r+4) ⧸ f.ker) := QuotientGroup.Quotient.group f.ker
  exact (@QuotientGroup.quotientMulEquivOfEq (elementaryRootGroup K (r+4))
      inferInstance (Subgroup.center (elementaryRootGroup K (r+4))) f.ker
      inferInstance f.normal_ker hf.symm).trans
    (QuotientGroup.quotientKerEquivRange f)

end SymmetricSubgroupAsymptotics.CFSGOrthogonalDSerreMatrices
