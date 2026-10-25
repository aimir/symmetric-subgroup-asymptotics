import SymmetricSubgroupAsymptotics.CFSGReeFFourBinarySeedOuterMatrix
import SymmetricSubgroupAsymptotics.CFSGFFourNormSparseWordMatrix

/-! The selected commutator entry is one literal entry of the arbitrary
other matrix. This uses the checked outer two-root matrix, and does not
assert any unproved formula for the ordered twelve-bit chart. -/
set_option autoImplicit false
set_option Elab.async false
namespace SymmetricSubgroupAsymptotics.CFSGReeFFourBinaryOuterEntryReduction
open CFSGReeFFourBinarySeedOuterMatrix
open scoped BigOperators

theorem outer_column_seven : ∀k : Fin 26,
    outerMatrix k 7=if k=7 then 1 else 0 := by
  decide +kernel

theorem outer_row_zero : ∀k : Fin 26,
    outerMatrix 0 k=(if k=0 then 1 else 0)+(if k=10 then 1 else 0) := by
  decide +kernel

theorem commutator_entry_eq (M : Matrix (Fin 26) (Fin 26) (ZMod 2)) :
    (M*outerMatrix-outerMatrix*M) 0 7=M 10 7 := by
  change (∑k : Fin 26,M 0 k*outerMatrix k 7)-
    (∑k : Fin 26,outerMatrix 0 k*M k 7)=M 10 7
  simp_rw [outer_column_seven,outer_row_zero]
  simp [add_mul,mul_ite,ite_mul,Finset.sum_add_distrib] <;> ring

end SymmetricSubgroupAsymptotics.CFSGReeFFourBinaryOuterEntryReduction
