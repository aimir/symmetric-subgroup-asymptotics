import SymmetricSubgroupAsymptotics.CFSGTwistedA2ProjectiveRadical
import SymmetricSubgroupAsymptotics.CFSGUnitaryRankTwoSylowAlignment
import SymmetricSubgroupAsymptotics.CFSGRankOneSylowRestrictionFaithful

/-! The whole original projective automorphism is determined by its
pointwise action on the actual radical and its two opposite Sylows.
The proved same-model two-cell cover supplies the global kernel proof. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Pointwise

namespace SymmetricSubgroupAsymptotics.CFSGTwistedAUnitaryCoordinates
open CFSGTwistedANaturalMatrices CFSGTwistedAUpperUnipotent

theorem rankTwo_reversalFixed_inv (q : CFSG.PrimePower) :
    (reversalFixed q 2)⁻¹ = reversalFixed q 2 := by
  apply Subtype.ext
  apply Subtype.ext
  apply Units.ext
  change (↑((signedReversalUnit (q.Extension 2) 2)⁻¹) : Mat (q.Extension 2) 2) =
    (signedReversalUnit (q.Extension 2) 2 : Mat (q.Extension 2) 2)
  rw [signedReversalUnit_inv_parity]
  norm_num

theorem rankTwoProjectiveWeyl_inv (q : CFSG.PrimePower) (hq : 3 ≤ q.order) :
    (rankTwoProjectiveCover q hq (reversalFixed q 2))⁻¹ =
      rankTwoProjectiveCover q hq (reversalFixed q 2) := by
  rw [← map_inv, rankTwo_reversalFixed_inv]

theorem rankTwoProjective_opposite_coe (q : CFSG.PrimePower) (hq : 3 ≤ q.order) :
    ((rankTwoProjectiveCover q hq (reversalFixed q 2) • rankTwoProjectiveSylow q hq :
      Sylow q.prime (CFSG.Models.TwistedA 2 q)) :
      Subgroup (CFSG.Models.TwistedA 2 q)) =
      (rankTwoOppositeSubgroup q).map (rankTwoProjectiveCover q hq) := by
  let w := reversalFixed q 2
  let pi := rankTwoProjectiveCover q hq
  change ((rankTwoUpperSubgroup q).map pi).map (MulAut.conj (pi w)).toMonoidHom =
    ((rankTwoUpperSubgroup q).map (MulAut.conj w).toMonoidHom).map pi
  simp only [Subgroup.map_map]
  have he : (MulAut.conj (pi w)).toMonoidHom.comp pi =
      pi.comp (MulAut.conj w).toMonoidHom := by
    ext g
    change pi w * pi g * (pi w)⁻¹ = pi (w * g * w⁻¹)
    rw [map_mul, map_mul, map_inv]
  rw [he]

theorem rankTwo_eq_one_of_fixed_radical_pair (q : CFSG.PrimePower) (hq : 3 ≤ q.order)
    [IsSimpleGroup (CFSG.Models.TwistedA 2 q)]
    (f : MulAut (CFSG.Models.TwistedA 2 q))
    (hfP : ((rankTwoUpperSubgroup q).map (rankTwoProjectiveCover q hq)).map f.toMonoidHom =
      (rankTwoUpperSubgroup q).map (rankTwoProjectiveCover q hq))
    (hfQ : ((rankTwoOppositeSubgroup q).map (rankTwoProjectiveCover q hq)).map f.toMonoidHom =
      (rankTwoOppositeSubgroup q).map (rankTwoProjectiveCover q hq))
    (hfix : ∀ u : (rankTwoUpperSubgroup q).map (rankTwoProjectiveCover q hq), f u.val = u.val) :
    f = 1 := by
  letI : Fact q.prime.Prime := ⟨q.prime_isPrime⟩
  letI : Finite (CFSG.Models.TwistedA 2 q) :=
    Finite.of_surjective (rankTwoProjectiveCover q hq) (rankTwoProjectiveCover_surjective q hq)
  apply CFSGRankOneSylowRestrictionFaithful.eq_one_of_fixed_root_and_opposite
    (rankTwoProjectiveSylow q hq) ((rankTwoUpperFlag q).map (rankTwoProjectiveCover q hq))
    (rankTwoProjectiveCover q hq (reversalFixed q 2))
    (rankTwo_projective_normalizer_eq_flag q hq).symm
    (rankTwoProjective_reversal_not_flag q hq) (rankTwoProjective_two_cells q hq) f
  · apply Sylow.ext
    change ((rankTwoUpperSubgroup q).map (rankTwoProjectiveCover q hq)).map f.toMonoidHom =
      (rankTwoUpperSubgroup q).map (rankTwoProjectiveCover q hq)
    exact hfP
  · apply Sylow.ext
    change (((rankTwoProjectiveCover q hq (reversalFixed q 2))⁻¹ • rankTwoProjectiveSylow q hq :
      Sylow q.prime (CFSG.Models.TwistedA 2 q)) :
        Subgroup (CFSG.Models.TwistedA 2 q)).map f.toMonoidHom =
      (((rankTwoProjectiveCover q hq (reversalFixed q 2))⁻¹ • rankTwoProjectiveSylow q hq :
        Sylow q.prime (CFSG.Models.TwistedA 2 q)) : Subgroup (CFSG.Models.TwistedA 2 q))
    rw [rankTwoProjectiveWeyl_inv, rankTwoProjective_opposite_coe]
    exact hfQ
  · exact hfix

end SymmetricSubgroupAsymptotics.CFSGTwistedAUnitaryCoordinates
