import SymmetricSubgroupAsymptotics.CFSGGTwoNaturalLieCentralizer
import SymmetricSubgroupAsymptotics.CFSGUnitConjugation

/-! Faithfulness of the actual natural action on the same integral
base-change image. The four Lie generators lie in that literal image;
no faithful original Lie representation is assumed. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Matrix TensorProduct
namespace SymmetricSubgroupAsymptotics.CFSGGTwoNaturalImageFaithful
open CFSGGTwoSerreMatrices CFSGGTwoNaturalLieCentralizer
open CFSG.Models.Chevalley
variable (K : Type) [Field K]

private theorem image_kernel_commutes (g : naturalGroup K)
    (hg : naturalImageAction K g = 1) (y : (foldedBaseChange K).range) :
    (g.val : Mat K) * y.val = y.val * (g.val : Mat K) := by
  have he : naturalImageAction K g y = y := by rw [hg]; rfl
  have hv := congrArg (fun z : (foldedBaseChange K).range => z.val) he
  change (g.val : Mat K) * y.val * (↑(g.val⁻¹) : Mat K) = y.val at hv
  exact (CFSGUnitConjugation.fix_iff_commute g.val y.val).mp hv

theorem natural_eq_one_of_image_action_eq_one (g : naturalGroup K)
    (hg : naturalImageAction K g = 1) : g = 1 := by
  apply natural_eq_one_of_lie_commutation K g
  · intro i
    let y : (foldedBaseChange K).range := ⟨positive K i, ⟨1 ⊗ₜ[ℤ]
      CFSGSerreDiagram.latticeGenerator CartanMatrix.G₂ (CartanMatrix.Generators.E i),
      foldedBaseChange_E K i⟩⟩
    exact image_kernel_commutes K g hg y
  · intro i
    let y : (foldedBaseChange K).range := ⟨negative K i, ⟨1 ⊗ₜ[ℤ]
      CFSGSerreDiagram.latticeGenerator CartanMatrix.G₂ (CartanMatrix.Generators.F i),
      foldedBaseChange_F K i⟩⟩
    exact image_kernel_commutes K g hg y

theorem naturalImageAction_injective : Function.Injective (naturalImageAction K) := by
  intro g h he
  have hk : naturalImageAction K (g⁻¹ * h) = 1 := by
    rw [map_mul, map_inv, he, inv_mul_cancel]
  exact inv_mul_eq_one.mp (natural_eq_one_of_image_action_eq_one K (g⁻¹ * h) hk)

end SymmetricSubgroupAsymptotics.CFSGGTwoNaturalImageFaithful
