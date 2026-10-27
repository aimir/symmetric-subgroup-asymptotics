import SymmetricSubgroupAsymptotics.CFSGMathieuTwentyThreeGoodSylowTwentyThree
import SymmetricSubgroupAsymptotics.SimplePrimeSylowIndexSquare

/-! Strict index square on the SAME pinned M23 source, using only its
faithful prime-degree representation, inherited simplicity/nonabelianness,
and order divisibility. No recovery or model equivalence is required. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics.CFSGMathieuTwentyThreeActualIndexSquare
open PrimitiveSocleRawStructure CFSG.Models.Presentations.M23
open CFSGMathieuTwentyThreeActualRepresentation
open CFSGMathieuTwentyThreeGoodSylowTwentyThree
local instance : Fact (Nat.Prime 23) := ⟨by decide⟩

theorem index_square [Finite Model] [IsSimpleGroup Model]
    (hn : ¬IsMulCommutative Model) (ell : ℕ) (hell : LeastProperIndex Model ell) :
    ell^2 < Nat.card Model := by
  letI : MulAction Model (Fin 23) := MulAction.compHom (Fin 23) permutationRepresentation
  letI : FaithfulSMul Model (Fin 23) := {
    eq_of_smul_eq_smul := fun {a b} hab =>
      permutationRepresentation_injective (Equiv.Perm.ext hab) }
  let a := pinnedX*pinnedY
  have hperm : orderOf (permutationRepresentation a) = 23 := by
    change orderOf (permutationRepresentation (pinnedX*pinnedY)) = 23
    rw [←Equiv.Perm.lcm_cycleType,pinnedProduct_cycleType]
    simp
  have ho : orderOf a = 23 :=
    (orderOf_injective permutationRepresentation permutationRepresentation_injective a).symm.trans hperm
  have hU : IsPGroup 23 (Subgroup.zpowers a) := by
    apply IsPGroup.of_card (n := 1)
    rw [Nat.card_zpowers,ho,pow_one]
  obtain ⟨P,hP⟩ := hU.exists_le_sylow
  have haP : a ∈ P := hP (Subgroup.mem_zpowers a)
  have hcard : Nat.card P = 23 :=
    SimpleInvolutionPrimeCycleGoodSylow.sylow_card_of_member_order P a haP ho prime_square_not_dvd
  have hmove : pinnedY • (0 : Fin 23) ≠ (0 : Fin 23) := by
    change permutationRepresentation (PresentedGroup.of (1 : Fin 2)) (0 : Fin 23) ≠ 0
    rw [permutationRepresentation_of_one]
    decide +kernel
  exact SimplePrimeSylowIndexSquare.least_index_square_of_moved_point
    hn P hcard pinnedY (0 : Fin 23) hmove ell hell

end SymmetricSubgroupAsymptotics.CFSGMathieuTwentyThreeActualIndexSquare
