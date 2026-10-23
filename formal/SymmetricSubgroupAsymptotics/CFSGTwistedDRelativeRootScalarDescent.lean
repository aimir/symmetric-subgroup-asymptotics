import SymmetricSubgroupAsymptotics.CFSGTwistedDProjectivePlaneLabel
import Mathlib.Tactic.Group

/-! If an actual relative element has an ambient highest-root word
with a relative conjugator, its coefficient is automatically in the
literal fixed field. This removes only the coefficient-extension seam;
no complete ambient-root recognition is assumed. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGTwistedDRelativeRootScalarDescent
open CFSGOrthogonalDSerreMatrices CFSGTwistedDRelativeElementaryGroup
open CFSGTwistedDRelativeUnipotentSylow CFSGTwistedDPlaneRootLine
open CFSGTwistedDRelativeHighestRoot CFSGTwistedDRelativeUnipotentCenterShape
open CFSGTwistedDProjectivePlaneLabel CFSGTwistedA2FixedField
open CFSGOrthogonalDIndexHighestRoot CFSGOrthogonalDIndexFlagVectors

theorem root_parameter_descends (s : ℕ) (q : CFSG.PrimePower)
    (x h : relativeRootGroup (s + 2) q) (b : q.Extension 2)
    (he : relativeInclusion s q x = relativeInclusion s q h *
      CFSGOrthogonalDIndexPairOperator.highestRoot (q.Extension 2) s b *
        (relativeInclusion s q h)⁻¹) :
    ∃ a : fixedField q, x = h * highestRoot s q a * h⁻¹ := by
  let k := h⁻¹ * x * h
  have hk : relativeInclusion s q k =
      CFSGOrthogonalDIndexPairOperator.highestRoot (q.Extension 2) s b := by
    change relativeInclusion s q (h⁻¹ * x * h) = _
    rw [map_mul, map_mul, map_inv, he]
    group
  have hm := congrArg
    (fun u : elementaryRootGroup (q.Extension 2) (s + 4) => (u.val : Mat (q.Extension 2) (s + 4))) hk
  change (k.val : Mat (q.Extension 2) (s + 4)) =
    ((highestInU (q.Extension 2) s b).val.val : Mat (q.Extension 2) (s + 4)) at hm
  rw [highestInU_val_plus] at hm
  let a : fixedField q := ⟨b, highest_parameter_fixed s q k b hm⟩
  have ha : k = highestRoot s q a := by
    apply Subtype.ext
    apply Units.ext
    change (k.val : Mat (q.Extension 2) (s + 4)) =
      ((highestInRelativeU s q a).val.val : Mat (q.Extension 2) (s + 4))
    rw [hm, highestInRelativeU_val]
  refine ⟨a, ?_⟩
  calc
    x = h * k * h⁻¹ := by dsimp only [k]; group
    _ = h * highestRoot s q a * h⁻¹ := by rw [ha]

end SymmetricSubgroupAsymptotics.CFSGTwistedDRelativeRootScalarDescent
