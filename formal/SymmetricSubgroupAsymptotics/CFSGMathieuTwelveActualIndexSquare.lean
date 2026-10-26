import SymmetricSubgroupAsymptotics.CFSGMathieuTwelveActualEquivalence
import SymmetricSubgroupAsymptotics.CFSGSimpleIndexTransport

/-! The genuine12-point representation has a proper point stabilizer of
index at most12. Exact pinned order95040 from the certified equivalence
therefore supplies the strict least-index square. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics.CFSGMathieuTwelveActualIndexSquare
open CFSG.Models.Presentations.M12 CFSGMathieuTwelveActualRepresentation
open PrimitiveSocleRawStructure

theorem least_index_le_twelve [Finite Model] (ell : ℕ) (hell : LeastProperIndex Model ell) :
    ell ≤ 12 := by
  letI : MulAction Model (Fin 12) := MulAction.compHom (Fin 12) permutationRepresentation
  let K := MulAction.stabilizer Model (0 : Fin 12)
  have hK : K ≠ ⊤ := by
    have hmove : CFSGMathieuTwelvePresentationWords.yPermutation (0 : Fin 12) ≠ 0 := by
      decide +kernel
    intro h
    have hg : PresentedGroup.of (1 : Fin 2) ∈ K := by rw [h]; trivial
    have he : permutationRepresentation (PresentedGroup.of (1 : Fin 2)) (0 : Fin 12) = 0 := hg
    rw [permutationRepresentation_of_one] at he
    exact hmove he
  have hi : K.index ≤ 12 := by
    simpa only [Nat.card_fin] using
      (MulAction.index_stabilizer Model (0 : Fin 12)).trans_le (Set.ncard_le_card _)
  exact (hell.2 K hK).trans hi

theorem index_square [Finite Model] [IsSimpleGroup Model] (ell : ℕ)
    (hell : LeastProperIndex Model ell) : ell ^ 2 < Nat.card Model := by
  rw [CFSGMathieuTwelveActualEquivalence.card]
  exact (Nat.pow_le_pow_left (least_index_le_twelve ell hell) 2).trans_lt
    (by decide : (12 : ℕ) ^ 2 < 95040)

end SymmetricSubgroupAsymptotics.CFSGMathieuTwelveActualIndexSquare
