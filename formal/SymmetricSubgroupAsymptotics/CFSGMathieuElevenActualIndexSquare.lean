import SymmetricSubgroupAsymptotics.CFSGMathieuElevenActualEquivalence
import SymmetricSubgroupAsymptotics.CFSGMathieuElevenGoodSylowTwo
import SymmetricSubgroupAsymptotics.CFSGSimpleIndexTransport

/-! The genuine11-point representation supplies a proper stabilizer of
index at most11. The separately certified equivalence gives exact order
7920 under inherited pinned simplicity, hence strict least-index square.
No subgroup census or expected model identification is used. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics.CFSGMathieuElevenActualIndexSquare
open CFSG.Models.Presentations.M11 CFSGMathieuElevenGoodSylowTwo PrimitiveSocleRawStructure

theorem least_index_le_eleven [Finite Model] (ell : ℕ) (hell : LeastProperIndex Model ell) :
    ell≤11 := by
  letI : MulAction Model (Fin 11) := MulAction.compHom (Fin 11) permutationRepresentation
  let K := MulAction.stabilizer Model (2 : Fin 11)
  have hK : K≠⊤ := by
    have hmove : CFSG.Certificates.Mathieu11.m11b (2 : Fin 11)≠2 := by decide +kernel
    intro h
    have hg : pinnedY∈K := by rw [h]; trivial
    have he : permutationRepresentation pinnedY (2 : Fin 11)=2 := hg
    rw [permutationRepresentation_pinnedY] at he
    exact hmove he
  have hi : K.index≤11 := by
    simpa only [Nat.card_fin] using
      (MulAction.index_stabilizer Model (2 : Fin 11)).trans_le (Set.ncard_le_card _)
  exact (hell.2 K hK).trans hi

theorem index_square [Finite Model] [IsSimpleGroup Model] (ell : ℕ)
    (hell : LeastProperIndex Model ell) : ell^2<Nat.card Model := by
  rw [CFSGMathieuElevenActualEquivalence.card]
  exact (Nat.pow_le_pow_left (least_index_le_eleven ell hell) 2).trans_lt
    (by decide : (11 : ℕ)^2<7920)

end SymmetricSubgroupAsymptotics.CFSGMathieuElevenActualIndexSquare
