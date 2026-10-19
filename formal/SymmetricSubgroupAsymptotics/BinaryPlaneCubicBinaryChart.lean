import SymmetricSubgroupAsymptotics.BinaryPlaneCubicScalarChart
import SymmetricSubgroupAsymptotics.BinaryPlaneNontrivialCubicFixedFree
import SymmetricSubgroupAsymptotics.BinaryTwistedQuartetPolynomial

/-! Every nonidentity order-three binary local operator has the exact
canonical binary matrix used by the two-seed quartet certificate. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.BinaryPlaneCubicBinaryChart
open BinaryPlanePermutationAffineEquiv
open BinaryPlaneCubicScalarChart (standard)
open BinaryTwistedQuartetPolynomial (cubic)
open BinaryQuadraticField (omega)

private theorem standard_cubic : ∀ v : Plane,
    standard (cubic v)=omega*standard v := by decide +kernel

theorem exists_chart (L : Linear) (hc : L^3=1) (hne : L≠1) :
    ∃ E : Plane ≃ₗ[ZMod 2] Plane, ∀ v, E (L v)=cubic (E v) := by
  obtain ⟨F,hF⟩ := BinaryPlaneCubicScalarChart.exists_chart L hc
    (BinaryPlaneNontrivialCubicFixedFree.fixedFree L hc hne)
  let E := F.trans standard.symm
  refine ⟨E,?_⟩
  intro v
  apply standard.injective
  change standard (standard.symm (F (L v)))=standard (cubic (E v))
  rw [standard.apply_symm_apply,hF,standard_cubic]
  change omega*F v=omega*standard (standard.symm (F v))
  rw [standard.apply_symm_apply]

end SymmetricSubgroupAsymptotics.BinaryPlaneCubicBinaryChart
