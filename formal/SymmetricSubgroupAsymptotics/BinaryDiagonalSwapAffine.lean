import SymmetricSubgroupAsymptotics.BinaryDiagonalSwapNormalCover
import SymmetricSubgroupAsymptotics.Non2PreE7AffineModel

/-! Specialization of the diagonal/swap kernel-cover theorem to the
existing faithful binary affine coordinate API. -/

set_option autoImplicit false
noncomputable section

namespace SymmetricSubgroupAsymptotics
namespace BinaryDiagonalSwap

variable {d : ℕ} (R : Subgroup (AffineModel.GLV 2 d))

theorem affine_linAut_injective : Function.Injective (AffineModel.linAut R) := by
  intro r s h
  apply Subtype.ext
  apply LinearEquiv.ext
  intro v
  exact congrArg (fun f : MulAut (Multiplicative (AffineModel.V 2 d)) ↦
    Multiplicative.toAdd (f (Multiplicative.ofAdd v))) h

theorem affine_translation_binary (v : Multiplicative (AffineModel.V 2 d)) :
    v * v = 1 := by
  apply Multiplicative.toAdd.injective
  funext i
  exact CharTwo.add_self_eq_zero _

theorem affine_irreducible (hirr : AffineModel.Irreducible R) :
    Irreducible (AffineModel.linAut R) := by
  intro S hS
  let A : AddSubgroup (AffineModel.V 2 d) :=
    { carrier := {v | Multiplicative.ofAdd v ∈ S}
      zero_mem' := S.one_mem
      add_mem' := by
        intro v w hv hw
        exact S.mul_mem hv hw
      neg_mem' := by
        intro v hv
        exact S.inv_mem hv }
  have hA : ∀ r ∈ R, ∀ v ∈ A, r v ∈ A := by
    intro r hr v hv
    exact hS ⟨r, hr⟩ (Multiplicative.ofAdd v) hv
  rcases hirr A hA with hb | ht
  · left
    apply le_antisymm _ bot_le
    intro v hv
    have hvA : Multiplicative.toAdd v ∈ A := hv
    have hv0 := AddSubgroup.mem_bot.mp (hb ▸ hvA)
    exact Subgroup.mem_bot.mpr (Multiplicative.toAdd.injective hv0)
  · right
    apply top_unique
    intro v _hv
    have hvA : Multiplicative.toAdd v ∈ A := by
      rw [ht]
      exact AddSubgroup.mem_top _
    exact hvA

theorem affine_normal_generating_tuples [Nonempty (Fin d)]
    (hirr : AffineModel.Irreducible R) {t : ℕ} (ht : 0 < t)
    (hQ : ∀ N : Subgroup (AffineModel.Aff R × Binary), N.Normal →
      ∃ x : Fin t → AffineModel.Aff R × Binary,
        Subgroup.normalClosure (Set.range x) = N) :
    ∀ N : Subgroup (Model (AffineModel.linAut R)), N.Normal →
      ∃ x : Fin t → Model (AffineModel.linAut R),
        Subgroup.normalClosure (Set.range x) = N :=
  normal_generating_tuples (AffineModel.linAut R) (affine_linAut_injective R)
    affine_translation_binary (affine_irreducible R hirr) ht hQ

end BinaryDiagonalSwap
end SymmetricSubgroupAsymptotics

end
