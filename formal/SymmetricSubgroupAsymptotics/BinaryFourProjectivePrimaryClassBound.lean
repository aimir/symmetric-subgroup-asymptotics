import SymmetricSubgroupAsymptotics.BinaryFourPrimaryClassCode
import SymmetricSubgroupAsymptotics.BinaryProjectiveLinearClassBound

/-! The proved primary-code ceiling transfers through the actual matrix
GL/linear-GL equivalence, the binary determinant-one map, and the full
central quotient. No exceptional-group identification is used. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.BinaryFourProjectivePrimaryClassBound
variable {K : Type*} [Field K] [Fintype K] [CharP K 2]

theorem general_class_card_le_fourteen (hK : Fintype.card K=2) :
    Nat.card (ConjClasses (Matrix.GeneralLinearGroup (Fin 4) K))≤14 := by
  let E := Matrix.GeneralLinearGroup.toLin (n := Fin 4) (R := K)
  have hd : Module.finrank K (Fin 4 → K)=4 := by rw [Module.finrank_pi]; rfl
  letI : Finite (ConjClasses (LinearMap.GeneralLinearGroup K (Fin 4 → K))) :=
    Finite.of_injective (BinaryFourPrimaryClassCode.classCode hK hd)
      (BinaryFourPrimaryClassCode.classCode_injective hK hd)
  have hc := Nat.card_le_card_of_surjective (ConjClasses.map E.symm.toMonoidHom)
    (ConjClasses.map_surjective E.symm.surjective)
  exact hc.trans (BinaryFourPrimaryClassCode.class_card_le_fourteen hK hd)

theorem special_class_card_le_fourteen (hK : Fintype.card K=2) :
    Nat.card (ConjClasses (Matrix.SpecialLinearGroup (Fin 4) K))≤14 :=
  (Nat.card_le_card_of_surjective
    (ConjClasses.map (BinaryProjectiveLinearClassBound.generalToSpecial hK))
    (ConjClasses.map_surjective
      (BinaryProjectiveLinearClassBound.generalToSpecial_surjective hK))).trans
    (general_class_card_le_fourteen hK)

theorem projective_class_card_le_fourteen (hK : Fintype.card K=2) :
    Nat.card (ConjClasses (Matrix.ProjectiveSpecialLinearGroup (Fin 4) K))≤14 := by
  letI : Finite (Matrix.SpecialLinearGroup (Fin 4) K) :=
    Finite.of_injective (fun A : Matrix.SpecialLinearGroup (Fin 4) K => A.val)
      Subtype.val_injective
  letI : Finite (ConjClasses (Matrix.SpecialLinearGroup (Fin 4) K)) :=
    Finite.of_surjective (@ConjClasses.mk (Matrix.SpecialLinearGroup (Fin 4) K) _)
      ConjClasses.mk_surjective
  exact (Nat.card_le_card_of_surjective
    (ConjClasses.map (QuotientGroup.mk' (Subgroup.center (Matrix.SpecialLinearGroup (Fin 4) K))))
    (ConjClasses.map_surjective (QuotientGroup.mk'_surjective _))).trans
      (special_class_card_le_fourteen hK)

end SymmetricSubgroupAsymptotics.BinaryFourProjectivePrimaryClassBound
