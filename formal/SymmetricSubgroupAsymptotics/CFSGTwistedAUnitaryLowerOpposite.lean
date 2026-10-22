import SymmetricSubgroupAsymptotics.CFSGTwistedAUnitaryOuterWeyl

/-! Exact lower-unitriangular characterization in the actual defining-
fixed group: every such element lies in the SAME signed-reversal
opposite of U. The proof uses literal reversal entries and scalar parity,
not an identification with a full classical matrix group. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section

namespace SymmetricSubgroupAsymptotics.CFSGTwistedAUnitaryCoordinates
open CFSGTwistedANaturalMatrices CFSGTwistedAUpperUnipotent

theorem signedReversal_conjugation_entry (K : Type) [Field K] (r : ℕ)
    (M : Mat K r) (i j : Fin (r + 1)) :
    ((signedReversalUnit K r : Mat K r) * M *
      (↑((signedReversalUnit K r)⁻¹) : Mat K r)) i j =
        signWeight K r i * M i.rev j.rev * signWeight K r j := by
  rw [signedReversalUnit_inv_eq_transpose]
  simp [Matrix.mul_apply, Matrix.transpose_apply, signedReversalUnit_apply,
    ite_mul, mul_ite, mul_assoc]

theorem reversal_inverse_conjugation (q : CFSG.PrimePower) (r : ℕ)
    (g : naturalFixed r q) :
    (reversalFixed q r)⁻¹ * g * reversalFixed q r =
      reversalFixed q r * g * (reversalFixed q r)⁻¹ := by
  apply Subtype.ext
  apply Subtype.ext
  apply Units.ext
  change (↑((signedReversalUnit (q.Extension 2) r)⁻¹) : Mat (q.Extension 2) r) *
      (g.val.val : Mat (q.Extension 2) r) *
        (signedReversalUnit (q.Extension 2) r : Mat (q.Extension 2) r) =
    (signedReversalUnit (q.Extension 2) r : Mat (q.Extension 2) r) *
      (g.val.val : Mat (q.Extension 2) r) *
        (↑((signedReversalUnit (q.Extension 2) r)⁻¹) : Mat (q.Extension 2) r)
  rw [signedReversalUnit_inv_parity]
  simp only [smul_mul_assoc, mul_smul_comm]

theorem lowerFixed_mem_opposite (q : CFSG.PrimePower) (r : ℕ)
    (g : naturalFixed r q)
    (hlower : ∀ i j, i < j → (g.val.val : Mat (q.Extension 2) r) i j = 0)
    (hdiag : ∀ i, (g.val.val : Mat (q.Extension 2) r) i i = 1) :
    g.val ∈ oppositeNaturalUnipotent q r := by
  let u := (reversalFixed q r)⁻¹ * g * reversalFixed q r
  have he : u = reversalFixed q r * g * (reversalFixed q r)⁻¹ :=
    reversal_inverse_conjugation q r g
  have hu : u.val ∈ naturalUnipotent r q := by
    refine ⟨⟨?_, ?_⟩, u.property⟩
    · intro i j hij
      change (u.val.val : Mat (q.Extension 2) r) i j = 0
      rw [he]
      change ((signedReversalUnit (q.Extension 2) r : Mat (q.Extension 2) r) *
        (g.val.val : Mat (q.Extension 2) r) *
          (↑((signedReversalUnit (q.Extension 2) r)⁻¹) : Mat (q.Extension 2) r)) i j = 0
      rw [signedReversal_conjugation_entry, hlower i.rev j.rev (Fin.rev_lt_rev.mpr hij),
        mul_zero, zero_mul]
    · intro i
      change (u.val.val : Mat (q.Extension 2) r) i i = 1
      rw [he]
      change ((signedReversalUnit (q.Extension 2) r : Mat (q.Extension 2) r) *
        (g.val.val : Mat (q.Extension 2) r) *
          (↑((signedReversalUnit (q.Extension 2) r)⁻¹) : Mat (q.Extension 2) r)) i i = 1
      rw [signedReversal_conjugation_entry, hdiag, mul_one]
      change ((-1 : q.Extension 2) ^ i.val) * ((-1 : q.Extension 2) ^ i.val) = 1
      rw [← mul_pow]
      simp
  refine ⟨u.val, hu, ?_⟩
  change (reversalFixed q r).val *
    ((reversalFixed q r).val⁻¹ * g.val * (reversalFixed q r).val) *
      (reversalFixed q r).val⁻¹ = g.val
  simp only [mul_assoc, mul_inv_cancel_left, mul_inv_cancel, mul_one]

end SymmetricSubgroupAsymptotics.CFSGTwistedAUnitaryCoordinates
