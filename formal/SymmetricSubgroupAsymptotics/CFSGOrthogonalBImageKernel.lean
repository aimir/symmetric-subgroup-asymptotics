import SymmetricSubgroupAsymptotics.CFSGOrthogonalBImageRealization
import SymmetricSubgroupAsymptotics.CFSGOrthogonalBElementaryCenter
import SymmetricSubgroupAsymptotics.CFSGUnitConjugation

/-! The actual quadratic-root action on the original B image has kernel
exactly the actual natural centre, away from characteristic two. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped TensorProduct
namespace SymmetricSubgroupAsymptotics.CFSGOrthogonalBSerreMatrices
open CFSG.Models.Chevalley

theorem orthogonalImage_centralizer (K : Type) [Field K] (r : ℕ) (h2 : (2:K)≠0) (A : Mat K (r+1))
    (hA : ∀x : Space (CartanMatrix.B (r+1)).transpose K,
      A*orthogonalBaseChange K (r+1) x=orthogonalBaseChange K (r+1) x*A) :
    ∃c : K,A=c • (1 : Mat K (r+1)) := by
  apply simple_root_centralizer r h2 A
  · intro i
    have hh := hA (1 ⊗ₜ[ℤ] CFSGSerreDiagram.latticeGenerator (CartanMatrix.B (r+1)).transpose (CartanMatrix.Generators.E i))
    simpa only [orthogonalBaseChange_E] using hh
  · intro i
    have hh := hA (1 ⊗ₜ[ℤ] CFSGSerreDiagram.latticeGenerator (CartanMatrix.B (r+1)).transpose (CartanMatrix.Generators.F i))
    simpa only [orthogonalBaseChange_F] using hh

theorem elementaryImageAction_ker (K : Type) [Field K] (r : ℕ) (h2 : (2:K)≠0) :
    (elementaryImageAction K (r+1)).ker=Subgroup.center (elementaryRootGroup K (r+1)) := by
  ext u
  change elementaryImageAction K (r+1) u=1↔u∈Subgroup.center (elementaryRootGroup K (r+1))
  constructor
  · intro hu
    apply (elementaryRootGroup_center_iff_scalar K r h2 u).mpr
    apply orthogonalImage_centralizer K r h2 (u.val : Mat K (r+1))
    intro x
    have hh := DFunLike.congr_fun hu ((orthogonalBaseChange K (r+1)).rangeRestrict x)
    have he := congrArg Subtype.val hh
    change (u.val : Mat K (r+1))*orthogonalBaseChange K (r+1) x*
      (↑(u.val⁻¹):Mat K (r+1))=orthogonalBaseChange K (r+1) x at he
    exact (CFSGUnitConjugation.fix_iff_commute u.val _).mp he
  · intro hu
    obtain ⟨c,hc⟩ := (elementaryRootGroup_center_iff_scalar K r h2 u).mp hu
    apply LinearEquiv.ext
    intro y
    apply Subtype.ext
    change (u.val : Mat K (r+1))*y.val*(↑(u.val⁻¹):Mat K (r+1))=y.val
    apply (CFSGUnitConjugation.fix_iff_commute u.val _).mpr
    rw [hc]
    simp only [smul_mul_assoc,mul_smul_comm,one_mul,mul_one]

def elementaryProjectiveActionEquiv (K : Type) [Field K] (r : ℕ) (h2 : (2:K)≠0) :
    elementaryProjective K (r+1)≃*(elementaryImageAction K (r+1)).range := by
  let f : elementaryRootGroup K (r+1) →*
      ((orthogonalBaseChange K (r+1)).range ≃ₗ[K]
        (orthogonalBaseChange K (r+1)).range) := elementaryImageAction K (r+1)
  have hf : f.ker=Subgroup.center (elementaryRootGroup K (r+1)) :=
    elementaryImageAction_ker K r h2
  letI : f.ker.Normal := f.normal_ker
  letI : Group (elementaryRootGroup K (r+1) ⧸ f.ker) := QuotientGroup.Quotient.group f.ker
  exact (@QuotientGroup.quotientMulEquivOfEq (elementaryRootGroup K (r+1))
      inferInstance (Subgroup.center (elementaryRootGroup K (r+1))) f.ker
      inferInstance f.normal_ker hf.symm).trans
    (QuotientGroup.quotientKerEquivRange f)

end SymmetricSubgroupAsymptotics.CFSGOrthogonalBSerreMatrices
