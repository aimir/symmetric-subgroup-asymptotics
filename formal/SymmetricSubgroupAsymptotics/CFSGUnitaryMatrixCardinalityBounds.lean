import SymmetricSubgroupAsymptotics.CFSGUnitarySpecialIsometryEquiv
import SymmetricSubgroupAsymptotics.CFSGTwistedAUnitaryProjectiveCover
import SymmetricSubgroupAsymptotics.CFSGProjectiveLinearCardComparison

/-! Uniform same-matrix unitary cardinal comparisons. The special
isometries are the actual natural fixed group, and its projective kernel
embeds in the already counted original SL centre. These are count inputs
for geometric automorphism reconstruction, not a claimed Outer bound. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGTwistedAUnitaryCoordinates
open CFSGTwistedANaturalMatrices CFSGTwistedAUpperUnipotent CFSGSerreOrdinaryTwists
open CFSGHermitianSimilitudeGroup

theorem signedReversal_hermitian (q : CFSG.PrimePower) (r : ℕ) :
    (signedReversalUnit (q.Extension 2) r : Mat (q.Extension 2) r).map
      (definingFieldAutomorphism q 2) = ((-1 : q.Extension 2) ^ r) •
        (signedReversalUnit (q.Extension 2) r : Mat (q.Extension 2) r).transpose := by
  have hh := signedMiddle_hermitian (q.Extension 2) (definingFieldAutomorphism q 2).toRingHom r
  rw [Matrix.map_neg _ (map_neg _) _] at hh
  simpa only [Matrix.transpose_neg, smul_neg, neg_inj] using hh

theorem unitary_linearSimilitudes_card_le (q : CFSG.PrimePower) (r : ℕ) :
    Nat.card (similitudes (definingFieldAutomorphism q 2) (signedReversalUnit (q.Extension 2) r)) ≤
      Nat.card (naturalFixed r q) * (q.order ^ 2 - 1) := by
  have hh := CFSGUnitaryHermitianScalarCardinality.similitudes_card_le_special_mul_field_units
    q ((-1 : q.Extension 2) ^ r) (signedReversalUnit (q.Extension 2) r)
    (signedReversal_hermitian q r) (0 : Fin (r + 1))
  rw [← Nat.card_congr (naturalFixedSpecialIsometryEquiv q r).toEquiv] at hh
  exact hh

def unitaryCoverKernelToSLCenter (q : CFSG.PrimePower) (s : ℕ) :
    (unitaryProjectiveCover q s).ker → Subgroup.center (NaturalSL (q.Extension 2) (s + 3)) := fun g =>
  ⟨naturalToSpecialLinear (q.Extension 2) (s + 3) g.val.val, by
    obtain ⟨c, hc⟩ := (unitaryProjectiveCover_kernel_iff_scalar q s g.val).mp g.property
    apply Subgroup.mem_center_iff.mpr
    intro M
    apply Subtype.ext
    change (M : Mat (q.Extension 2) (s + 3)) * (g.val.val.val : Mat (q.Extension 2) (s + 3)) =
      (g.val.val.val : Mat (q.Extension 2) (s + 3)) * (M : Mat (q.Extension 2) (s + 3))
    rw [hc]
    simp only [mul_smul_comm, smul_mul_assoc, Matrix.mul_one, Matrix.one_mul]⟩

theorem unitaryCoverKernelToSLCenter_injective (q : CFSG.PrimePower) (s : ℕ) :
    Function.Injective (unitaryCoverKernelToSLCenter q s) := by
  intro g h he
  apply Subtype.ext
  apply Subtype.ext
  apply (naturalSpecialLinearEquiv (q.Extension 2) (s + 3)).injective
  exact congrArg Subtype.val he

theorem unitaryProjectiveCover_kernel_card_le (q : CFSG.PrimePower) (s : ℕ) :
    Nat.card (unitaryProjectiveCover q s).ker ≤ s + 4 := by
  have hh := Nat.card_le_card_of_injective (unitaryCoverKernelToSLCenter q s)
    (unitaryCoverKernelToSLCenter_injective q s)
  have hc := CFSGProjectiveLinearCardComparison.specialLinear_center_card_le_dimension
    (F := q.Extension 2) (n := Fin (s + 3 + 1))
  exact hh.trans (by simpa only [Fintype.card_fin] using hc)

theorem unitary_naturalFixed_card_le_projective_mul_dimension (q : CFSG.PrimePower) (s : ℕ) :
    Nat.card (naturalFixed (s + 3) q) ≤
      (s + 4) * Nat.card (CFSG.Models.TwistedA (s + 3) q) := by
  let f := unitaryProjectiveCover q s
  have he : Nat.card (naturalFixed (s + 3) q) = Nat.card f.ker * Nat.card f.range := by
    rw [← f.ker.card_mul_index, Subgroup.index_ker]
  rw [f.range_eq_top_of_surjective (unitaryProjectiveCover_surjective q s), Subgroup.card_top] at he
  rw [he]
  exact Nat.mul_le_mul_right _ (unitaryProjectiveCover_kernel_card_le q s)

end SymmetricSubgroupAsymptotics.CFSGTwistedAUnitaryCoordinates
