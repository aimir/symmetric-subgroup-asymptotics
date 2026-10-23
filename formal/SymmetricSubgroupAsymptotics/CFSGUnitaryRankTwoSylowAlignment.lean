import SymmetricSubgroupAsymptotics.CFSGUnitaryRankTwoBruhat
import SymmetricSubgroupAsymptotics.CFSGUnitaryRankTwoFlagNormalizer
import SymmetricSubgroupAsymptotics.CFSGRankOneSylowAlignment

/-! Inner alignment of an actual ordered pair of rank-two unitary
Sylows in the original projective model, using the proved matrix
two-cell cover and full normalizer equality. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Pointwise

namespace SymmetricSubgroupAsymptotics.CFSGTwistedAUnitaryCoordinates
open CFSGTwistedANaturalMatrices CFSGTwistedAUpperUnipotent

def rankTwoProjectiveSylow (q : CFSG.PrimePower) (hq : 3 ≤ q.order) :
    Sylow q.prime (CFSG.Models.TwistedA 2 q) := by
  letI : Fact q.prime.Prime := ⟨q.prime_isPrime⟩
  exact (rankTwoNaturalSylow q).mapSurjective (rankTwoProjectiveCover_surjective q hq)

theorem rankTwoProjectiveSylow_coe (q : CFSG.PrimePower) (hq : 3 ≤ q.order) :
    (rankTwoProjectiveSylow q hq : Subgroup (CFSG.Models.TwistedA 2 q)) =
      (rankTwoUpperSubgroup q).map (rankTwoProjectiveCover q hq) := rfl

theorem rankTwoProjective_reversal_not_flag (q : CFSG.PrimePower) (hq : 3 ≤ q.order) :
    rankTwoProjectiveCover q hq (reversalFixed q 2) ∉
      (rankTwoUpperFlag q).map (rankTwoProjectiveCover q hq) := by
  intro h
  have he := Subgroup.comap_map_eq_self (rankTwoProjectiveCover_kernel_le_flag q hq)
  have hw : reversalFixed q 2 ∈ rankTwoUpperFlag q := by
    rw [← he]
    exact h
  have hu := (rankTwoUpperFlag_mem_iff q _).mp hw
  have hz : (signedReversalUnit (q.Extension 2) 2 : Mat (q.Extension 2) 2) 2 0 = 0 :=
    hu (by decide)
  norm_num [signedReversalUnit_apply, Fin.rev, signWeight] at hz

theorem rankTwoProjective_two_cells (q : CFSG.PrimePower) (hq : 3 ≤ q.order)
    (x : CFSG.Models.TwistedA 2 q) :
    x ∈ (rankTwoUpperFlag q).map (rankTwoProjectiveCover q hq) ∨
      ∃ (b : (rankTwoUpperFlag q).map (rankTwoProjectiveCover q hq))
        (u : rankTwoProjectiveSylow q hq),
        x = b.val * rankTwoProjectiveCover q hq (reversalFixed q 2) * u.val := by
  let f := rankTwoProjectiveCover q hq
  obtain ⟨g, rfl⟩ := rankTwoProjectiveCover_surjective q hq x
  rcases rankTwo_upper_or_reversal_cell q g⁻¹ with h | ⟨u, b, he⟩
  · left
    exact ⟨g, by simpa only [inv_inv] using (rankTwoUpperFlag q).inv_mem h, rfl⟩
  · right
    refine ⟨⟨f b.val⁻¹, ⟨b.val⁻¹, (rankTwoUpperFlag q).inv_mem b.property, rfl⟩⟩,
      ⟨f u.val⁻¹, ⟨u.val⁻¹, (rankTwoUpperSubgroup q).inv_mem u.property, rfl⟩⟩, ?_⟩
    have hh := congrArg (fun a : naturalFixed 2 q => f a⁻¹) he
    simpa only [inv_inv, mul_inv_rev, map_mul, map_inv] using hh

theorem rankTwoProjective_exists_inner_fix_pair (q : CFSG.PrimePower) (hq : 3 ≤ q.order)
    (f : MulAut (CFSG.Models.TwistedA 2 q)) :
    ∃ g : CFSG.Models.TwistedA 2 q,
      (MulAut.conj g * f) • rankTwoProjectiveSylow q hq = rankTwoProjectiveSylow q hq ∧
      (MulAut.conj g * f) •
          (rankTwoProjectiveCover q hq (reversalFixed q 2) • rankTwoProjectiveSylow q hq) =
        rankTwoProjectiveCover q hq (reversalFixed q 2) • rankTwoProjectiveSylow q hq := by
  letI : Fact q.prime.Prime := ⟨q.prime_isPrime⟩
  letI : Finite (CFSG.Models.TwistedA 2 q) :=
    Finite.of_surjective (rankTwoProjectiveCover q hq) (rankTwoProjectiveCover_surjective q hq)
  exact CFSGRankOneSylowAlignment.exists_inner_fix_pair (rankTwoProjectiveSylow q hq)
    ((rankTwoUpperFlag q).map (rankTwoProjectiveCover q hq))
    (rankTwoProjectiveCover q hq (reversalFixed q 2))
    (rankTwo_projective_normalizer_eq_flag q hq).symm
    (rankTwoProjective_reversal_not_flag q hq) (rankTwoProjective_two_cells q hq) f

end SymmetricSubgroupAsymptotics.CFSGTwistedAUnitaryCoordinates
