import SymmetricSubgroupAsymptotics.CFSGProjectiveLinearCardComparison
import Mathlib.FieldTheory.Finite.Basic
import Mathlib.GroupTheory.SpecificGroups.Cyclic

/-! The exact finite-field gcd replaces the dimension-only central
scalar budget in the actual original PGL/PSL order comparison. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGProjectiveLinearGcdCardComparison
open CFSGProjectiveLinearCardComparison CFSGTypeAGeneralLinearCardBound
variable {F I : Type*} [Field F] [Finite F] [Fintype I] [DecidableEq I] [Nonempty I]

theorem specialLinear_center_card_eq_gcd :
    Nat.card (Subgroup.center (Matrix.SpecialLinearGroup I F))=
      (Nat.card F-1).gcd (Fintype.card I) := by
  letI : Fintype F := Fintype.ofFinite F
  have he : rootsOfUnity (Fintype.card I) F=(powMonoidHom (Fintype.card I):Fˣ→*Fˣ).ker := by
    ext u
    simp only [mem_rootsOfUnity,MonoidHom.mem_ker,powMonoidHom_apply]
  rw [Nat.card_congr (Matrix.SpecialLinearGroup.center_equiv_rootsOfUnity'
    (n:=I) (R:=F) (Classical.arbitrary I)).toEquiv,he,
    IsCyclic.card_powMonoidHom_ker,Nat.card_units]

theorem projective_card_le_gcd_mul_specialProjective :
    Nat.card (Matrix.ProjGenLinGroup I F) ≤
      (Nat.card F-1).gcd (Fintype.card I)*
        Nat.card (Matrix.ProjectiveSpecialLinearGroup I F) := by
  have hSL := (Subgroup.center (Matrix.SpecialLinearGroup I F)).card_mul_index
  change Nat.card (Subgroup.center (Matrix.SpecialLinearGroup I F))*
    Nat.card (Matrix.ProjectiveSpecialLinearGroup I F)=
      Nat.card (Matrix.SpecialLinearGroup I F) at hSL
  rw [specialLinear_center_card_eq_gcd] at hSL
  have hGL := generalLinear_card_le_specialLinear_mul_units (F:=F) (n:=I)
  apply Nat.le_of_mul_le_mul_right (c:=Nat.card Fˣ)
  · rw [projective_card_mul_units]
    exact hGL.trans_eq (congrArg (fun a:ℕ=>a*Nat.card Fˣ) hSL.symm)
  · exact Nat.card_pos

end SymmetricSubgroupAsymptotics.CFSGProjectiveLinearGcdCardComparison
