import SymmetricSubgroupAsymptotics.AlternatingSignedImageNormalGenerators
import SymmetricSubgroupAsymptotics.OriginalAbelianKernelSolvable
import SymmetricSubgroupAsymptotics.LinearThreeSolvable

/-! The actual signed four-block image is soluble and its order has
only one cubic factor, independent of its correlated binary kernel. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace SymmetricSubgroupAsymptotics.AlternatingSignedImageStructure
open AlternatingSignedImageNormalGenerators
open LinearSemidirectSubgroupKernelChart

theorem model_card : Nat.card Model=2^7*3 := by
  have hc : Nat.card ESign=2^4 := by
    change Nat.card (⊤ : Submodule (ZMod 2) (Fin 4 → ZMod 2))=2^4
    rw [Nat.card_congr (Submodule.topEquiv :
      (⊤ : Submodule (ZMod 2) (Fin 4 → ZMod 2)) ≃ₗ[ZMod 2] (Fin 4 → ZMod 2)).toEquiv,
      Nat.card_fun,Nat.card_fin,Nat.card_zmod]
  change Nat.card ESign.toSubmodule=2^4 at hc
  rw [SemidirectProduct.card,Nat.card_congr Multiplicative.toAdd,hc,
    Nat.card_eq_fintype_card,Fintype.card_perm,Fintype.card_fin]
  norm_num

theorem card_dvd_single_cubic (B : Subgroup Model) : Nat.card B∣2^7*3 := by
  simpa only [model_card] using B.card_subgroup_dvd_card

theorem isSolvable (B : Subgroup Model) : IsSolvable B := by
  letI : IsSolvable (Equiv.Perm (Fin 4)) := naturalS4_isSolvable
  let pi := LinearSemidirectActualImageKernelChart.top action B
  let A := LinearSemidirectActualImageKernelChart.kernelModule action B
  let E := LinearSemidirectActualImageKernelChart.originalKernelChart action B
  letI : IsSolvable (Image action B) := solvable_of_solvable_injective
    (f := (Image action B).subtype) Subtype.val_injective
  exact E.isSolvable_of_solvable_base pi A

end SymmetricSubgroupAsymptotics.AlternatingSignedImageStructure
