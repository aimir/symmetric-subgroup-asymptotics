import SymmetricSubgroupAsymptotics.CFSGLinearBlockOrderSelected
import SymmetricSubgroupAsymptotics.PrimitiveSmallExceptionalSocleFactors

/-! Faithful binary representations of dimension at most two have soluble
image. In particular no noncommutative finite simple group can occur as
such a constituent. The proof uses the literal GL order divisor. -/
set_option autoImplicit false
noncomputable section
open scoped Classical

namespace SymmetricSubgroupAsymptotics.CFSGSmallBinaryLinearSolubility

theorem solvable_of_faithful_dimension_le_two
    {S W : Type} [Group S] [Finite S] [AddCommGroup W] [Module (ZMod 2) W]
    [FiniteDimensional (ZMod 2) W]
    (tau : Representation (ZMod 2) S W) (hf : Function.Injective tau)
    (hd : Module.finrank (ZMod 2) W ≤ 2) : IsSolvable S := by
  let b := Module.finBasis (ZMod 2) W
  let phi : S →* Matrix.GeneralLinearGroup (Fin (Module.finrank (ZMod 2) W)) (ZMod 2) :=
    (Matrix.GeneralLinearGroup.toLin' b).symm.toMonoidHom.comp tau.asGroupHom
  have hphi : Function.Injective phi := by
    intro g h he
    apply hf
    exact congrArg Units.val ((Matrix.GeneralLinearGroup.toLin' b).symm.injective he)
  have hgl : Nat.card (Matrix.GeneralLinearGroup
      (Fin (Module.finrank (ZMod 2) W)) (ZMod 2)) =
      fullLinearOrder 2 (Module.finrank (ZMod 2) W) := by
    rw [Matrix.card_GL_field]
    simp only [fullLinearOrder, ZMod.card]
  have hdiv : Nat.card S ∣ fullLinearOrder 2 (Module.finrank (ZMod 2) W) :=
    hgl ▸ Subgroup.card_dvd_of_injective phi hphi
  have hdsmall : Module.finrank (ZMod 2) W = 0 ∨ Module.finrank (ZMod 2) W = 1 ∨
      Module.finrank (ZMod 2) W = 2 := by omega
  have hsmall : fullLinearOrder 2 (Module.finrank (ZMod 2) W) ∣ 6 := by
    rcases hdsmall with h | h | h <;> rw [h] <;> decide
  exact isSolvable_of_card_dvd_small_head_degree 6 (Or.inl rfl) (hdiv.trans hsmall)

theorem three_le_dimension_of_noncommutative_simple
    {S W : Type} [Group S] [Finite S] [IsSimpleGroup S]
    [AddCommGroup W] [Module (ZMod 2) W] [FiniteDimensional (ZMod 2) W]
    (tau : Representation (ZMod 2) S W) (hf : Function.Injective tau)
    (hnc : ¬ IsMulCommutative S) : 3 ≤ Module.finrank (ZMod 2) W := by
  by_contra hd
  letI : IsSolvable S := solvable_of_faithful_dimension_le_two tau hf (by omega)
  exact hnc (isMulCommutative_iff.mpr (IsSimpleGroup.comm_iff_isSolvable.mpr inferInstance))

end SymmetricSubgroupAsymptotics.CFSGSmallBinaryLinearSolubility
