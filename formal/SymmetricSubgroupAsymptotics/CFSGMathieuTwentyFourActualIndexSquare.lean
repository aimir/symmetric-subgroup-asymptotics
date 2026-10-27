import SymmetricSubgroupAsymptotics.CFSGMathieuTwentyFourGoodSylowTwentyThree
import SymmetricSubgroupAsymptotics.SimplePrimeSylowSuccessorIndexSquare

/-! Strict least-index square for the SAME pinned M24 source. Its literal
generator images do not commute. The faithful24-action with one23-cycle
then invokes the generic successor-degree transfer argument. No actual
M24 order, recovery, surjectivity, or extra noncommutativity premise is used. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics.CFSGMathieuTwentyFourActualIndexSquare
open PrimitiveSocleRawStructure CFSG.Models.Presentations.M24
open CFSGMathieuTwentyFourActualRepresentation CFSGMathieuTwentyFourGoodSylowTwentyThree
local instance : Fact (Nat.Prime 23) := ⟨by decide⟩

theorem model_noncommutative : ¬ IsMulCommutative Model := by
  intro h
  letI : IsMulCommutative Model := h
  have he := congrArg permutationRepresentation (mul_comm' pinnedX pinnedY)
  change permutationRepresentation
      ((PresentedGroup.of (0 : Fin 2)) * (PresentedGroup.of (1 : Fin 2))) =
    permutationRepresentation
      ((PresentedGroup.of (1 : Fin 2)) * (PresentedGroup.of (0 : Fin 2))) at he
  simp only [map_mul, permutationRepresentation_of_zero, permutationRepresentation_of_one] at he
  have hmove :
      (CFSGMathieuTwentyFourPresentationWords.xPermutation *
        CFSGMathieuTwentyFourPresentationWords.yPermutation) (0 : Fin 24) ≠
      (CFSGMathieuTwentyFourPresentationWords.yPermutation *
        CFSGMathieuTwentyFourPresentationWords.xPermutation) (0 : Fin 24) := by
    decide +kernel
  exact hmove (congrArg (fun σ : Equiv.Perm (Fin 24) => σ (0 : Fin 24)) he)

theorem index_square [Finite Model] [IsSimpleGroup Model] (ell : ℕ)
    (hell : LeastProperIndex Model ell) : ell ^ 2 < Nat.card Model := by
  letI : MulAction Model (Fin 24) := MulAction.compHom (Fin 24) permutationRepresentation
  letI : FaithfulSMul Model (Fin 24) := {
    eq_of_smul_eq_smul := fun {a b} hab =>
      permutationRepresentation_injective (Equiv.Perm.ext hab) }
  apply SimplePrimeSylowSuccessorIndexSquare.least_index_square_of_prime_cycle (p := 23)
    model_noncommutative (by decide) (pinnedX * pinnedY) ?_ ell hell
  have he : MulAction.toPermHom Model (Fin (23 + 1)) (pinnedX * pinnedY) =
      permutationRepresentation (pinnedX * pinnedY) := by
    ext i
    rfl
  rw [he]
  exact pinnedProduct_cycleType

end SymmetricSubgroupAsymptotics.CFSGMathieuTwentyFourActualIndexSquare
