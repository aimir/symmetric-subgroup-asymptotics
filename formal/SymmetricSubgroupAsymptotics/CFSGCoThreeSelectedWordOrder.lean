import SymmetricSubgroupAsymptotics.CFSGCoThreeSelectedTraceAction
import SymmetricSubgroupAsymptotics.NoncommutativeTwoFibreGenerators
import SymmetricSubgroupAsymptotics.LinearActionSelectedPointPeriod

/-! Noncommutativity supplies genuine units in the two pinned Co3 matrix
fibres. Their SAME positive product has the checked point period14.
Thus its actual element order is divisible by14; every faithful action
of this model has at least9points. No matrix invertibility, whole-matrix
power or ambient group-order certificate is assumed. -/
set_option autoImplicit false
noncomputable section
open scoped Matrix
namespace SymmetricSubgroupAsymptotics.CFSGCoThreeSelectedWordOrder
open CFSGCoThreeSelectedTraceData CFSGCoThreeSelectedTraceAction

abbrev Model := CFSG.Models.MatrixGroups.Co3.Model

def unitAction : Model →* ((Fin 22 → ZMod 2) ≃ₗ[ZMod 2] (Fin 22 → ZMod 2)) :=
  (LinearMap.GeneralLinearGroup.generalLinearEquiv (ZMod 2) (Fin 22 → ZMod 2)).toMonoidHom.comp
    (Matrix.GeneralLinearGroup.toLin.toMonoidHom.comp
      (Subgroup.closure (CFSG.Models.MatrixData.generators 2 22
        CFSG.Models.MatrixGroups.Co3.rows1 CFSG.Models.MatrixGroups.Co3.rows2)).subtype)

def unitEnd : Model →* Module.End (ZMod 2) (Fin 22 → ZMod 2) :=
  LinearEquiv.automorphismGroup.toLinearMapMonoidHom.comp unitAction

theorem exists_fourteen_dvd_orderOf (hn : ¬ IsMulCommutative Model) :
    ∃ g : Model, 14 ∣ orderOf g := by
  obtain ⟨x,hx,y,hy,hxa,hyb,_⟩ :=
    NoncommutativeTwoFibreGenerators.matrix_model_generators 2 22
      CFSG.Models.MatrixGroups.Co3.rows1 CFSG.Models.MatrixGroups.Co3.rows2 hn
  let xm : Model := ⟨x,Subgroup.subset_closure hx⟩
  let ym : Model := ⟨y,Subgroup.subset_closure hy⟩
  let g : Model := xm*ym
  have hraw : unitEnd g = wordEnd := by
    apply LinearMap.ext
    intro v
    change ((x : Matrix (Fin 22) (Fin 22) (ZMod 2))*
      (y : Matrix (Fin 22) (Fin 22) (ZMod 2))) *ᵥ v = a *ᵥ (b *ᵥ v)
    rw [hxa,hyb]
    exact (Matrix.mulVec_mulVec v a b).symm
  exact ⟨g,LinearActionSelectedPointPeriod.fourteen_dvd_orderOf unitAction g wordEnd hraw
    (vectors 0) return_fourteen nonreturn_two nonreturn_seven⟩

theorem nine_le_card_of_faithful_permutation_action {X : Type*} [Finite X]
    (hn : ¬ IsMulCommutative Model) (f : Model →* Equiv.Perm X)
    (hf : Function.Injective f) : 9 ≤ Nat.card X := by
  obtain ⟨g,hg⟩ := exists_fourteen_dvd_orderOf hn
  apply PermutationTwicePrimeOrderDegree.nine_le_card_of_fourteen_dvd_orderOf (f g)
  rw [orderOf_injective f hf g]
  exact hg

end SymmetricSubgroupAsymptotics.CFSGCoThreeSelectedWordOrder
