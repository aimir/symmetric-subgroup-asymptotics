import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoPrimitiveSixteenRows4And7LinearRelations
import SymmetricSubgroupAsymptotics.OddPrimeDihedralNormalChain
import SymmetricSubgroupAsymptotics.DirectProductNormalGenerators
import SymmetricSubgroupAsymptotics.CyclicQuotientSocles
import Mathlib.GroupTheory.NoncommCoprod

/-! The actual row4/7 complements are surjective images of C3 × D6 and
D6 × D6. Normal-generator bounds descend along these displayed maps;
no claim about their kernels or group orders is needed. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped Classical

namespace SymmetricSubgroupAsymptotics
namespace PrimitiveAffineDegreeTwoPrimitiveSixteenRows4And7Complements

open PrimitiveAffineDegreeTwoPrimitiveSixteenRows8And10LinearRelations
open PrimitiveAffineDegreeTwoPrimitiveSixteenRows4And7LinearRelations

abbrev C3 := Multiplicative (ZMod 3)
abbrev ModelFour := C3 × DihedralGroup 3
abbrev ModelSeven := DihedralGroup 3 × DihedralGroup 3

def leftRotationMap : C3 →* LinearGroup where
  toFun i := a ^ i.toAdd.val
  map_one' := rfl
  map_mul' := by
    intro i j
    apply LinearEquiv.ext
    intro x
    revert i j x
    decide +kernel

def leftDihedralMap : DihedralGroup 3 →* LinearGroup where
  toFun
    | .r i => a ^ i.val
    | .sr i => d * a ^ i.val
  map_one' := rfl
  map_mul' := by
    rintro (i | i) (j | j) <;>
      apply LinearEquiv.ext <;> intro x <;> revert i j x <;> decide +kernel

def rightDihedralMap : DihedralGroup 3 →* LinearGroup where
  toFun
    | .r i => b ^ i.val
    | .sr i => s * b ^ i.val
  map_one' := rfl
  map_mul' := by
    rintro (i | i) (j | j) <;>
      apply LinearEquiv.ext <;> intro x <;> revert i j x <;> decide +kernel

theorem rotation_right_commute (i : C3) (j : DihedralGroup 3) :
    Commute (leftRotationMap i) (rightDihedralMap j) := by
  change leftRotationMap i * rightDihedralMap j = rightDihedralMap j * leftRotationMap i
  cases j with
  | r j => apply LinearEquiv.ext; intro x; revert i j x; decide +kernel
  | sr j => apply LinearEquiv.ext; intro x; revert i j x; decide +kernel

theorem factors_commute (i j : DihedralGroup 3) :
    Commute (leftDihedralMap i) (rightDihedralMap j) := by
  change leftDihedralMap i * rightDihedralMap j = rightDihedralMap j * leftDihedralMap i
  cases i with
  | r i =>
    cases j with
    | r j => apply LinearEquiv.ext; intro x; revert i j x; decide +kernel
    | sr j => apply LinearEquiv.ext; intro x; revert i j x; decide +kernel
  | sr i =>
    cases j with
    | r j => apply LinearEquiv.ext; intro x; revert i j x; decide +kernel
    | sr j => apply LinearEquiv.ext; intro x; revert i j x; decide +kernel

def productAction4 : ModelFour →* LinearGroup :=
  leftRotationMap.noncommCoprod rightDihedralMap rotation_right_commute

def productAction7 : ModelSeven →* LinearGroup :=
  leftDihedralMap.noncommCoprod rightDihedralMap factors_commute

theorem productAction4_a : productAction4 (Multiplicative.ofAdd 1, 1) = a := by
  apply LinearEquiv.ext; intro x; revert x; decide +kernel
theorem productAction4_b : productAction4 (1, .r 1) = b := by
  apply LinearEquiv.ext; intro x; revert x; decide +kernel
theorem productAction4_s : productAction4 (1, .sr 0) = s := by
  apply LinearEquiv.ext; intro x; revert x; decide +kernel
theorem productAction7_a : productAction7 (.r 1, 1) = a := by
  apply LinearEquiv.ext; intro x; revert x; decide +kernel
theorem productAction7_b : productAction7 (1, .r 1) = b := by
  apply LinearEquiv.ext; intro x; revert x; decide +kernel
theorem productAction7_s : productAction7 (1, .sr 0) = s := by
  apply LinearEquiv.ext; intro x; revert x; decide +kernel
theorem productAction7_d : productAction7 (.sr 0, 1) = d := by
  apply LinearEquiv.ext; intro x; revert x; decide +kernel

theorem productAction4_range : productAction4.range = R4 := by
  apply le_antisymm
  · rintro _ ⟨⟨i, j⟩, rfl⟩
    change a ^ i.toAdd.val * rightDihedralMap j ∈ R4
    apply R4.mul_mem (R4.pow_mem a_mem4 _)
    cases j with
    | r j => exact R4.pow_mem b_mem4 _
    | sr j => exact R4.mul_mem s_mem4 (R4.pow_mem b_mem4 _)
  · apply (Subgroup.closure_le _).mpr
    rintro _ ⟨i, rfl⟩
    fin_cases i
    · exact ⟨(Multiplicative.ofAdd 1, 1), productAction4_a⟩
    · exact ⟨(1, .r 1), productAction4_b⟩
    · exact ⟨(1, .sr 0), productAction4_s⟩

theorem productAction7_range : productAction7.range = R7 := by
  apply le_antisymm
  · rintro _ ⟨⟨i, j⟩, rfl⟩
    change leftDihedralMap i * rightDihedralMap j ∈ R7
    apply R7.mul_mem
    · cases i with
      | r i => exact R7.pow_mem a_mem7 _
      | sr i => exact R7.mul_mem d_mem7 (R7.pow_mem a_mem7 _)
    · cases j with
      | r j => exact R7.pow_mem b_mem7 _
      | sr j => exact R7.mul_mem s_mem7 (R7.pow_mem b_mem7 _)
  · apply (Subgroup.closure_le _).mpr
    rintro _ ⟨i, rfl⟩
    fin_cases i
    · exact ⟨(.r 1, 1), productAction7_a⟩
    · exact ⟨(1, .r 1), productAction7_b⟩
    · exact ⟨(1, .sr 0), productAction7_s⟩
    · exact ⟨(.sr 0, 1), productAction7_d⟩

def complementMap4 : ModelFour →* R4 :=
  (MulEquiv.subgroupCongr productAction4_range).toMonoidHom.comp
    productAction4.rangeRestrict
def complementMap7 : ModelSeven →* R7 :=
  (MulEquiv.subgroupCongr productAction7_range).toMonoidHom.comp
    productAction7.rangeRestrict

theorem complementMap4_surjective : Function.Surjective complementMap4 :=
  (MulEquiv.subgroupCongr productAction4_range).surjective.comp
    productAction4.rangeRestrict_surjective
theorem complementMap7_surjective : Function.Surjective complementMap7 :=
  (MulEquiv.subgroupCongr productAction7_range).surjective.comp
    productAction7.rangeRestrict_surjective

theorem normal_generating_pairs4 :
    ∀ N : Subgroup R4, N.Normal →
      ∃ x : Fin 2 → R4, Subgroup.normalClosure (Set.range x) = N := by
  letI : Fact (Nat.Prime 3) := ⟨by decide⟩
  exact normal_generating_tuples_of_surjective complementMap4 complementMap4_surjective
    (normal_generating_tuples_prod
      (normal_generating_singletons_of_isCyclic (G := C3))
      (OddPrimeDihedralNormalChain.normal_generating_singletons (p := 3) (by decide)))

theorem normal_generating_pairs7 :
    ∀ N : Subgroup R7, N.Normal →
      ∃ x : Fin 2 → R7, Subgroup.normalClosure (Set.range x) = N := by
  letI : Fact (Nat.Prime 3) := ⟨by decide⟩
  exact normal_generating_tuples_of_surjective complementMap7 complementMap7_surjective
    (normal_generating_tuples_prod
      (OddPrimeDihedralNormalChain.normal_generating_singletons (p := 3) (by decide))
      (OddPrimeDihedralNormalChain.normal_generating_singletons (p := 3) (by decide)))

end PrimitiveAffineDegreeTwoPrimitiveSixteenRows4And7Complements
end SymmetricSubgroupAsymptotics

end
