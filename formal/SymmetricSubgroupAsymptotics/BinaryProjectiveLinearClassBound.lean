import SymmetricSubgroupAsymptotics.BinaryLinearCyclicClassCode
import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
import Mathlib.LinearAlgebra.Matrix.ProjectiveSpecialLinearGroup

/-! The binary cyclic-coefficient cover bounds the actual matrix GL, SL
and full-center projective SL models. Over a field of order two every
invertible determinant is one; all transfers are literal surjective group
maps, without exceptional simple-group identifications. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.BinaryProjectiveLinearClassBound
variable {K I : Type*} [Field K] [Fintype K] [Fintype I] [DecidableEq I]

def generalToSpecial (hK : Fintype.card K = 2) :
    Matrix.GeneralLinearGroup I K →* Matrix.SpecialLinearGroup I K where
  toFun g := ⟨g.val,
    (BinaryMonicPolynomialCode.zero_or_one hK g.val.det).resolve_left g.det_ne_zero⟩
  map_one' := Subtype.ext rfl
  map_mul' _ _ := Subtype.ext rfl

theorem generalToSpecial_surjective (hK : Fintype.card K = 2) :
    Function.Surjective (generalToSpecial (I := I) hK) := by
  intro g
  exact ⟨Matrix.SpecialLinearGroup.toGL g, Subtype.ext rfl⟩

theorem general_class_card_le_codes (hK : Fintype.card K = 2) :
    Nat.card (ConjClasses (Matrix.GeneralLinearGroup I K)) ≤
      (BinaryWeightedMultisetCodes.codes (Fintype.card I)).card := by
  let E := Matrix.GeneralLinearGroup.toLin (n := I) (R := K)
  letI : Finite (ConjClasses (LinearMap.GeneralLinearGroup K (I → K))) :=
    Finite.of_injective (BinaryLinearCyclicClassCode.classCode (V := I → K))
      (BinaryLinearCyclicClassCode.classCode_injective hK)
  have hc := Nat.card_le_card_of_surjective (ConjClasses.map E.symm.toMonoidHom)
    (ConjClasses.map_surjective E.symm.surjective)
  refine hc.trans ?_
  simpa only [Module.finrank_pi] using
    BinaryLinearCyclicClassCode.class_card_le_codes (V := I → K) hK

theorem special_class_card_le_codes (hK : Fintype.card K = 2) :
    Nat.card (ConjClasses (Matrix.SpecialLinearGroup I K)) ≤
      (BinaryWeightedMultisetCodes.codes (Fintype.card I)).card :=
  (Nat.card_le_card_of_surjective (ConjClasses.map (generalToSpecial hK))
    (ConjClasses.map_surjective (generalToSpecial_surjective hK))).trans
      (general_class_card_le_codes hK)

theorem projective_class_card_le_codes (hK : Fintype.card K = 2) :
    Nat.card (ConjClasses (Matrix.ProjectiveSpecialLinearGroup I K)) ≤
      (BinaryWeightedMultisetCodes.codes (Fintype.card I)).card :=
  (Nat.card_le_card_of_surjective
    (ConjClasses.map (QuotientGroup.mk' (Subgroup.center (Matrix.SpecialLinearGroup I K))))
    (ConjClasses.map_surjective (QuotientGroup.mk'_surjective _))).trans
      (special_class_card_le_codes hK)

theorem projective_four_class_card_le (hK : Fintype.card K = 2) :
    Nat.card (ConjClasses (Matrix.ProjectiveSpecialLinearGroup (Fin 4) K)) ≤ 18 := by
  simpa only [Fintype.card_fin, BinaryWeightedMultisetCodes.card_codes_four] using
    projective_class_card_le_codes (I := Fin 4) hK

theorem projective_six_class_card_le (hK : Fintype.card K = 2) :
    Nat.card (ConjClasses (Matrix.ProjectiveSpecialLinearGroup (Fin 6) K)) ≤ 104 := by
  simpa only [Fintype.card_fin, BinaryWeightedMultisetCodes.card_codes_six] using
    projective_class_card_le_codes (I := Fin 6) hK

end SymmetricSubgroupAsymptotics.BinaryProjectiveLinearClassBound
