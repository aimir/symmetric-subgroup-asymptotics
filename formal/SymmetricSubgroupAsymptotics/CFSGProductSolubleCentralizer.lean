import SymmetricSubgroupAsymptotics.CFSGProductFactorCentralizer
import Mathlib.GroupTheory.Solvable

/-! A second coordinate factor embeds in the actual centralizer of the
first. Consequently, a soluble coordinate centralizer forces a product
of non-soluble factors to have only that coordinate. -/
set_option autoImplicit false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics.CFSGProductSolubleCentralizer
open CFSGProductFactorCentralizer

variable {I S : Type} [Group S]

def otherFactorHom (i j : I) (hji : j ≠ i) :
    S →* Subgroup.centralizer (factor (S := S) i : Set (I → S)) where
  toFun a := ⟨factorHom j a, mem_centralizer_of_coordinate_one i _ (by
    simp [factorHom, hji, Ne.symm hji])⟩
  map_one' := Subtype.ext ((factorHom j).map_one)
  map_mul' a b := Subtype.ext ((factorHom j).map_mul a b)

theorem otherFactorHom_injective (i j : I) (hji : j ≠ i) :
    Function.Injective (otherFactorHom (S := S) i j hji) := by
  intro a b hab
  exact factorHom_injective j (congrArg Subtype.val hab)

theorem index_eq_of_soluble_centralizer (i : I)
    [IsSolvable (Subgroup.centralizer (factor (S := S) i : Set (I → S)))]
    (hns : ¬ IsSolvable S) (j : I) : j = i := by
  by_contra hji
  exact hns (solvable_of_solvable_injective
    (otherFactorHom_injective (S := S) i j hji))

theorem subsingleton_of_soluble_centralizer (i : I)
    [IsSolvable (Subgroup.centralizer (factor (S := S) i : Set (I → S)))]
    (hns : ¬ IsSolvable S) : Subsingleton I :=
  ⟨fun j k => (index_eq_of_soluble_centralizer i hns j).trans
    (index_eq_of_soluble_centralizer i hns k).symm⟩

end SymmetricSubgroupAsymptotics.CFSGProductSolubleCentralizer
