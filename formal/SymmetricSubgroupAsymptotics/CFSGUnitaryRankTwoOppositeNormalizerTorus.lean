import SymmetricSubgroupAsymptotics.CFSGUnitaryRankTwoProjectiveNormalizer
import SymmetricSubgroupAsymptotics.CFSGUnitaryRankTwoDiagonalTorus

/-! The full opposite-upper normalizer intersection in the original
rank-two quotient lies in its literal torus. This keeps the actual
normalizers, rather than replacing them by chosen flag subgroups. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section

namespace SymmetricSubgroupAsymptotics.CFSGTwistedAUnitaryCoordinates
open CFSGTwistedANaturalMatrices CFSGTwistedAUpperUnipotent

theorem rankTwo_natural_pair_normalizer_le_torus (q : CFSG.PrimePower) :
    Subgroup.normalizer (rankTwoUpperSubgroup q : Set _) ⊓
      Subgroup.normalizer (rankTwoOppositeSubgroup q : Set _) ≤ (rankTwoNaturalTorus q).range := by
  rintro g ⟨hgU, hgV⟩
  let w := reversalFixed q 2
  have hQP : (rankTwoOppositeSubgroup q).map (MulAut.conj w⁻¹).toMonoidHom =
      rankTwoUpperSubgroup q := by
    change ((rankTwoUpperSubgroup q).map (MulAut.conj w).toMonoidHom).map _ = _
    rw [Subgroup.map_map]
    have hh : (MulAut.conj w⁻¹).toMonoidHom.comp (MulAut.conj w).toMonoidHom =
        MonoidHom.id _ := by
      ext x
      simp [MulAut.conj_apply, mul_assoc]
    rw [hh, Subgroup.map_id]
  have hkN := (rankTwoOppositeSubgroup q).le_normalizer_map (MulAut.conj w⁻¹).toMonoidHom
    ⟨g, hgV, rfl⟩
  rw [hQP] at hkN
  let k : naturalFixed 2 q := w⁻¹ * g * w
  have hkupper := rankTwo_natural_normalizer_upper q k hkN
  have hupper := rankTwo_natural_normalizer_upper q g hgU
  apply rankTwo_diagonal_mem_torus q g
  intro i j hij
  rcases lt_or_gt_of_ne hij with hij | hji
  · have hh : (k.val.val : Mat (q.Extension 2) 2) i.rev j.rev = 0 :=
      hkupper (Fin.rev_lt_rev.mpr hij)
    have he : k = w * g * w⁻¹ := reversal_inverse_conjugation q 2 g
    rw [he] at hh
    change ((signedReversalUnit (q.Extension 2) 2 : Mat (q.Extension 2) 2) *
      (g.val.val : Mat (q.Extension 2) 2) *
      (↑((signedReversalUnit (q.Extension 2) 2)⁻¹) : Mat (q.Extension 2) 2)) i.rev j.rev = 0 at hh
    rw [signedReversal_conjugation_entry] at hh
    simp only [Fin.rev_rev] at hh
    have hi : signWeight (q.Extension 2) 2 i.rev ≠ 0 := pow_ne_zero _ (neg_ne_zero.mpr one_ne_zero)
    have hj : signWeight (q.Extension 2) 2 j.rev ≠ 0 := pow_ne_zero _ (neg_ne_zero.mpr one_ne_zero)
    exact (mul_eq_zero.mp ((mul_eq_zero.mp hh).resolve_right hj)).resolve_left hi
  · exact hupper hji

theorem rankTwo_projective_pair_normalizer_le_torus (q : CFSG.PrimePower) (hq : 3 ≤ q.order) :
    Subgroup.normalizer ((rankTwoUpperSubgroup q).map (rankTwoProjectiveCover q hq) : Set _) ⊓
      Subgroup.normalizer ((rankTwoOppositeSubgroup q).map (rankTwoProjectiveCover q hq) : Set _) ≤
        (rankTwoProjectiveTorus q hq).range := by
  rintro x ⟨hxP, hxQ⟩
  obtain ⟨g, rfl⟩ := rankTwoProjectiveCover_surjective q hq x
  have hP := (rankTwo_projective_normalizer_iff q hq (rankTwoUpperSubgroup q)
    (rankTwoUpperSubgroup_isPGroup q) g).mp hxP
  have hQ := (rankTwo_projective_normalizer_iff q hq (rankTwoOppositeSubgroup q)
    ((rankTwoUpperSubgroup_isPGroup q).map _) g).mp hxQ
  obtain ⟨z, hz⟩ := rankTwo_natural_pair_normalizer_le_torus q ⟨hP, hQ⟩
  exact ⟨z, congrArg (rankTwoProjectiveCover q hq) hz⟩

end SymmetricSubgroupAsymptotics.CFSGTwistedAUnitaryCoordinates
