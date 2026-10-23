import SymmetricSubgroupAsymptotics.CFSGTwistedDAllRankPairedTorus

/-! The actual finite-field norm supplies every nonzero fixed-field
scale of a positive terminal pole, using literal relative torus words. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Matrix
namespace SymmetricSubgroupAsymptotics.CFSGTwistedDRelativeNormScaling
open CFSGOrthogonalDSerreMatrices CFSGOrthogonalDGenerationForkTorus
open CFSGTwistedDRelativeElementaryGroup CFSGTwistedDAllRankPairedTorus
open CFSGTwistedDRelativeTorusParameters CFSGTwistedA2FixedField
open CFSGSerreOrdinaryTwists

theorem normHom_surjective (q : CFSG.PrimePower) : Function.Surjective (normHom q) := by
  intro a
  have ha : definingFieldAutomorphism q 2 ((a : fixedField q) : q.Extension 2) =
      ((a : fixedField q) : q.Extension 2) := (a : fixedField q).property
  obtain ⟨c, hc⟩ := CFSGTwistedA2UnipotentArrays.exists_norm_eq_fixed q
    ((a : fixedField q) : q.Extension 2) ha
  have hc0 : c ≠ 0 := by
    intro h
    rw [h, zero_mul] at hc
    exact Units.ne_zero a ((fixedField q).subtype.injective hc.symm)
  refine ⟨Units.mk0 c hc0, ?_⟩
  apply Units.ext
  apply Subtype.ext
  change (((normHom q (Units.mk0 c hc0) : (fixedField q)ˣ) : fixedField q) : q.Extension 2) = _
  rw [normHom_val]
  exact hc

theorem pairedTorus_positive_axis (n : ℕ) (q : CFSG.PrimePower)
    (c : (q.Extension 2)ˣ) (a : q.Extension 2) :
    (((pairedTorus n q c).val : Mat (q.Extension 2) (n + 2)) *ᵥ
      Pi.single (Sum.inl (pen n)) a) =
        Pi.single (Sum.inl (pen n))
          ((((normHom q c : (fixedField q)ˣ) : fixedField q) : q.Extension 2) * a) := by
  rw [pairedTorus_val, Matrix.diagonal_mulVec_single, normHom_val]
  simp only [diagonal, chainDiagonal, forkDiagonal, if_true, unitFrobenius_val]

theorem exists_scale_positive_axis (n : ℕ) (q : CFSG.PrimePower) (a : (fixedField q)ˣ) :
    ∃ u : relativeRootGroup n q,
      (u.val : Mat (q.Extension 2) (n + 2)) *ᵥ
        Pi.single (Sum.inl (pen n)) (((a : fixedField q) : q.Extension 2)) =
          Pi.single (Sum.inl (pen n)) 1 := by
  obtain ⟨c, hc⟩ := normHom_surjective q a⁻¹
  refine ⟨⟨(pairedTorus n q c).val, pairedTorus_mem n q c⟩, ?_⟩
  change (((pairedTorus n q c).val : Mat (q.Extension 2) (n + 2)) *ᵥ _) = _
  rw [pairedTorus_positive_axis, hc]
  have ha : (((a⁻¹ : (fixedField q)ˣ) : fixedField q) : q.Extension 2) *
      (((a : (fixedField q)ˣ) : fixedField q) : q.Extension 2) = 1 := by
    exact congrArg (fun x : fixedField q => (x : q.Extension 2)) (Units.inv_mul a)
  rw [ha]

end SymmetricSubgroupAsymptotics.CFSGTwistedDRelativeNormScaling
