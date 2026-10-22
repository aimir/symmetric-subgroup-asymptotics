import SymmetricSubgroupAsymptotics.CFSGTwistedAUnitaryCentralDerived
import SymmetricSubgroupAsymptotics.CFSGTwistedAUnitaryNaturalRadicalSupport

/-! The actual central upper radical is the literal extreme-entry
transvection. Its precise inverse parameter remains a valid central
fixed parameter in every characteristic. These are actual units for
the next outer Weyl word, not assumed root membership. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section

namespace SymmetricSubgroupAsymptotics.CFSGTwistedAUnitaryUpperArrays
variable {K J : Type*} [CommRing K] [Fintype J] [DecidableEq J]

theorem upperArray_central (b : K) :
    upperArray (0 : J → K) 0 b = 1 + Matrix.single (.inl ()) (.inr (.inr ())) b := by
  ext p q
  rcases p with u | (i | u) <;> rcases q with v | (j | v)
  all_goals try cases u
  all_goals try cases v
  all_goals simp [upperArray, Matrix.add_apply, Matrix.one_apply, Matrix.single_apply]

end SymmetricSubgroupAsymptotics.CFSGTwistedAUnitaryUpperArrays

namespace SymmetricSubgroupAsymptotics.CFSGTwistedAUnitaryCoordinates
open CFSGTwistedANaturalMatrices CFSGTwistedAUpperUnipotent
open CFSGTwistedAUnitaryUpperArrays CFSGTwistedAUnitaryNaturalRadical
open CFSGSerreOrdinaryTwists

theorem central_inverse_condition {K : Type*} [Field K] (sigma : K ≃+* K)
    (eps : K) (heps : eps = 1 ∨ eps = -1) (t : K)
    (ht : sigma t + eps * t = 0) :
    sigma (-eps * t⁻¹) + eps * (-eps * t⁻¹) = 0 := by
  rcases heps with rfl | rfl
  · simp only [one_mul] at ht
    have hs : sigma t = -t := by
      calc
        _ = (sigma t + t) - t := by ring
        _ = -t := by rw [ht]; ring
    simp [map_mul, map_neg, map_inv₀, hs]
  · have hs : sigma t = t := by
      apply sub_eq_zero.mp
      simpa only [neg_one_mul, sub_eq_add_neg] using ht
    simp [map_mul, map_neg, map_inv₀, hs]

theorem central_inverse_parameter_condition (q : CFSG.PrimePower) (s : ℕ)
    (t : q.Extension 2) (ht : Condition q s 0 t) :
    Condition q s 0 (-parity q s * t⁻¹) := by
  apply (centralCondition_iff q s _).mpr
  exact central_inverse_condition (definingFieldAutomorphism q 2) (parity q s)
    (neg_one_pow_eq_or (q.Extension 2) s) t ((centralCondition_iff q s t).mp ht)

theorem radicalCentral_matrix (q : CFSG.PrimePower) (s : ℕ)
    (t : q.Extension 2) (ht : Condition q s 0 t) :
    ((radicalElement q s 0 t ht).val.val : Mat (q.Extension 2) (s + 2)) =
      1 + Matrix.single (0 : Fin (s + 3)) (Fin.last (s + 2)) t := by
  rw [radicalElement_matrix, firstRow_zero_eq, upperArray_central]
  ext i j
  obtain ⟨p, rfl⟩ := (splitEquiv s).surjective i
  obtain ⟨q', rfl⟩ := (splitEquiv s).surjective j
  simp only [Matrix.reindex_apply, Matrix.submatrix_apply, Equiv.symm_apply_apply]
  change (1 + Matrix.single (.inl ()) (.inr (.inr ())) t) p q' =
    (1 + Matrix.single (splitEquiv s (.inl ())) (splitEquiv s (.inr (.inr ()))) t)
      (splitEquiv s p) (splitEquiv s q')
  simp only [Matrix.add_apply, Matrix.one_apply, Matrix.single_apply,
    (splitEquiv s).injective.eq_iff]

def centralFixed (q : CFSG.PrimePower) (s : ℕ)
    (t : q.Extension 2) (ht : Condition q s 0 t) : naturalFixed (s + 2) q :=
  ⟨(radicalElement q s 0 t ht).val, (radicalElement q s 0 t ht).property.2⟩

end SymmetricSubgroupAsymptotics.CFSGTwistedAUnitaryCoordinates
