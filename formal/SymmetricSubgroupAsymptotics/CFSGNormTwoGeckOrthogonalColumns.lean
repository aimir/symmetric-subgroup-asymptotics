import SymmetricSubgroupAsymptotics.CFSGNormTwoGeckQuadratic
import SymmetricSubgroupAsymptotics.CFSGNormTwoRootNeighbors

/-! Orthogonal norm-two roots give genuine zero mixed second columns.
This is a geometric root-pairing computation on the same actual lattice,
prior to folding any named Cartan diagram. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Matrix
namespace SymmetricSubgroupAsymptotics.CFSGNormTwoGeckOrthogonalColumns
open CFSGIntegerMatrixPairing CFSGNormTwoRootPairing CFSGNormTwoRootStrings
open CFSGNormTwoGeckColumns CFSGNormTwoGeckQuadratic
variable {n : Type*} [Fintype n] [DecidableEq n]
    (A : Matrix n n ℤ) (hs : A.transpose=A) (hp : (rationalMatrix A).PosDef)
    [Fintype (Roots A)] [DecidableEq (Roots A)]
    (b : (rootPairing A hs hp).Base)

theorem integerPairing_eq_cartan (i j : b.support) :
    integerPairing A (i:Roots A).val (j:Roots A).val=b.cartanMatrix i j := by
  apply (Int.cast_injective (α:=ℚ))
  rw [←pairing_cast A hs hp]
  exact (RootPairing.Base.algebraMap_cartanMatrixIn_apply ℤ b i j).symm

theorem E_v_of_pairing_zero (i j : b.support)
    (hij : integerPairing A (i:Roots A).val (j:Roots A).val=0) :
    RootPairing.GeckConstruction.e i *ᵥRootPairing.GeckConstruction.v b j=0 := by
  apply E_v_zero A hs hp b i j
  · intro he
    have hv := congrArg Subtype.val he
    rw [negative_val A hs hp] at hv
    rw [hv,map_neg,(i:Roots A).property] at hij
    norm_num at hij
  · rw [CFSGNormTwoRootNeighbors.root_add_mem_iff A hs hp,hij]
    norm_num

theorem E_mul_second_of_pairing_zero (i j : b.support)
    (hij : integerPairing A (i:Roots A).val (j:Roots A).val=0) :
    RootPairing.GeckConstruction.e i * secondMatrix A hs hp b j=0 := by
  apply Matrix.ext_of_mulVec_single
  intro k
  rw [←Matrix.mulVec_mulVec,second_on_basis,Matrix.zero_mulVec]
  split_ifs
  · exact E_v_of_pairing_zero A hs hp b i j hij
  · exact Matrix.mulVec_zero _

end SymmetricSubgroupAsymptotics.CFSGNormTwoGeckOrthogonalColumns
