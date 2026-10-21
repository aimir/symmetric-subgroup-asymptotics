import SymmetricSubgroupAsymptotics.S8Seed29NormalizerRoots
import SymmetricSubgroupAsymptotics.FiniteGeneratorWord
import Mathlib.Tactic.FinCases

/-! One selected larger-seed inclusion for original8T29. Three ordinary
word equations exhibit an actual point-conjugate of original8T35 inside
the root adjunction. No order calculation is a theorem premise. -/
set_option autoImplicit false
noncomputable section
open scoped Pointwise
namespace SymmetricSubgroupAsymptotics.S8Seed29Root31Contains128
open S8Seed29LeftCosets

def conjugator : Ambient where
  toFun := ![0, 1, 3, 4, 2, 7, 5, 6]
  invFun := ![0, 1, 4, 2, 3, 6, 7, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def sourceGenerators : Fin 6 → Ambient :=
  Matrix.vecCons (representatives (S8Seed29NormalizerRoots.roots 31))
    BinaryMenuCayley8T29.generators

def certificate : FiniteGeneratorWordCertificate
    (fun j => (MulAut.conj conjugator) (BinaryMenuCayley8T35.generators j))
    sourceGenerators where
  words := ![(.mul (.mul (.generator 0) (.mul (.inv (.generator 4)) (.generator 0))) (.mul (.inv (.generator 4)) (.mul (.generator 0) (.generator 4)))), (.mul (.mul (.generator 0) (.generator 4)) (.mul (.generator 5) (.inv (.generator 0)))), (.mul (.inv (.generator 0)) (.mul (.generator 4) (.inv (.generator 0))))]
  equations := by
    intro j
    fin_cases j <;> apply Equiv.ext <;> intro x <;> revert x <;> decide +kernel

theorem contains_seed :
    MulAut.conj conjugator • Subgroup.closure (Set.range BinaryMenuCayley8T35.generators) ≤
      H ⊔ Subgroup.closure {representatives (S8Seed29NormalizerRoots.roots 31)} := by
  change (Subgroup.closure (Set.range BinaryMenuCayley8T35.generators)).map
    (MulAut.conj conjugator).toMonoidHom ≤ _
  apply Subgroup.map_le_iff_le_comap.mpr
  apply (Subgroup.closure_le _).mpr
  rintro _ ⟨j, rfl⟩
  change (MulAut.conj conjugator) (BinaryMenuCayley8T35.generators j) ∈
    (H ⊔ Subgroup.closure {representatives (S8Seed29NormalizerRoots.roots 31)} : Subgroup Ambient)
  rw [← certificate.equations j]
  have h := (certificate.words j).eval_mem_closure sourceGenerators
  simpa only [sourceGenerators, Matrix.range_cons, Subgroup.closure_union, sup_comm] using h

end SymmetricSubgroupAsymptotics.S8Seed29Root31Contains128
end
