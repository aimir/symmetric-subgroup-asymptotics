import SymmetricSubgroupAsymptotics.CFSGSymplecticPauliPrimeIndex
import SymmetricSubgroupAsymptotics.CFSGSymplecticSmallClassBounds
import SymmetricSubgroupAsymptotics.CFSGSymplecticSharpComponentOrderCube

/-! The actual 3-local index27 pays the last binary rank-three literal
symplectic scaled class packet. Classes96 and outer3 are independently
proved on this SAME full elementary projective quotient. No census,
GU order, low-index assumption or original-C simplicity is supplied. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGSymplecticBinaryRankThreePauliClassPacket
open PrimitiveSocleRawStructure CFSGReduction CFSGSymplecticSerreMatrices

theorem elementary_scaled_class_cube_le_proper_index (q : CFSG.PrimePower) (hq : q.order=2)
    [IsSimpleGroup (elementaryProjective q.Field 3)] [Finite (elementaryProjective q.Field 3)]
    (H : Subgroup (elementaryProjective q.Field 3)) (hH : H≠⊤) :
    25*(Nat.card (ConjClasses (elementaryProjective q.Field 3))*
      Nat.card (Outer (elementaryProjective q.Field 3)))^3 ≤ 3^H.index := by
  have hp : q.prime=2 ∧ q.exponent=1 :=
    Nat.Prime.pow_inj' q.prime_isPrime Nat.prime_two q.exponent_pos.ne'
      (by decide : (1:ℕ)≠0) (show q.prime^q.exponent=2^1 from hq)
  letI : CharP q.Field 2 := by rw [←hp.1]; infer_instance
  have hclasses : Nat.card (ConjClasses (elementaryProjective q.Field 3)) ≤ 96 :=
    (Nat.card_le_card_of_surjective
      (ConjClasses.map (QuotientGroup.mk' (Subgroup.center (elementaryRootGroup q.Field 3))))
      (ConjClasses.map_surjective (QuotientGroup.mk'_surjective _))).trans
        (CFSGSymplecticSmallClassBounds.binary_rankThree q.Field (q.card_field.trans hq))
  have houter : Nat.card (Outer (elementaryProjective q.Field 3)) ≤ 3 := by
    simpa only [Nat.reduceAdd,CFSGFiniteFieldAutomorphisms.primePower_card_ringAut q,hp.2,
      Nat.mul_one] using
      CFSGSymplecticPointRootLabels.binary_outer_card_le (K := q.Field) 2 (by decide)
  exact ((Nat.mul_le_mul_left 25 (Nat.pow_le_pow_left (Nat.mul_le_mul hclasses houter) 3)).trans
    (by decide +kernel : 25*((96:ℕ)*3)^3 ≤ 3^27)).trans
      (Nat.pow_le_pow_right (by decide)
        (CFSGSymplecticPauliPrimeIndex.projective_proper_index_ge_twentySeven q.Field H hH))

end SymmetricSubgroupAsymptotics.CFSGSymplecticBinaryRankThreePauliClassPacket
