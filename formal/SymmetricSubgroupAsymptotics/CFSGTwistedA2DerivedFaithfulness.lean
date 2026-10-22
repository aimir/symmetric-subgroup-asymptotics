import SymmetricSubgroupAsymptotics.CFSGTwistedA2DerivedWords
import SymmetricSubgroupAsymptotics.CFSGTwistedA2FieldWitness
import SymmetricSubgroupAsymptotics.CFSGSimpleProjectiveDescent

/-! Genuine nontriviality and projective natural correspondence for the
ORIGINAL rank-two twisted-A source, under its original q != 2 guard.
Only the final projective equivalence uses the genuine original model's
simplicity instance. All preceding nontriviality is unconditional. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped commutatorElement

namespace SymmetricSubgroupAsymptotics.CFSGTwistedA2HighestRootUnits
open CFSGTwistedANaturalMatrices CFSGTwistedA2FieldWitness

theorem derived_image_exists_not_center (q : CFSG.PrimePower) (hq : 3 ≤ q.order) :
    ∃ g : commutator (OriginalFixedA 2 q),
      (twistedDerivedAction 2 q).rangeRestrict g ∉
        Subgroup.center (twistedDerivedAction 2 q).range := by
  obtain ⟨t, a, ht, htskew, ha, haone, hafix⟩ := exists_skew_and_fixed_scalar q hq
  let g := deltaDerived q t htskew 1 (one_pow _)
  let h := deltaDerived q t htskew a hafix
  refine ⟨g, ?_⟩
  intro hc
  have hh := congrArg Subtype.val ((Subgroup.mem_center_iff.mp hc)
    ((twistedDerivedAction 2 q).rangeRestrict h))
  change twistedDerivedAction 2 q h * twistedDerivedAction 2 q g =
    twistedDerivedAction 2 q g * twistedDerivedAction 2 q h at hh
  dsimp only [g, h] at hh
  rw [deltaDerived_image, deltaDerived_image] at hh
  have hcomm : ⁅naturalElementaryAction (q.Extension 2) 2 (delta (q.Extension 2) t 1),
      naturalElementaryAction (q.Extension 2) 2 (delta (q.Extension 2) t a)⁆ = 1 :=
    commutatorElement_eq_one_iff_mul_comm.mpr hh.symm
  have hk : ⁅delta (q.Extension 2) t 1, delta (q.Extension 2) t a⁆ ∈
      (naturalElementaryAction (q.Extension 2) 2).ker := by
    change naturalElementaryAction (q.Extension 2) 2 _ = 1
    rw [map_commutatorElement]
    exact hcomm
  rw [naturalElementaryAction_ker (q.Extension 2) 2 (by decide)] at hk
  exact delta_commutator_not_scalar (q.Extension 2) t ht a ha haone
    ((naturalElementary_center_iff_scalar (q.Extension 2) 2 (by decide) _).mp hk)

theorem derived_projective_nontrivial (q : CFSG.PrimePower) (hq : 3 ≤ q.order) :
    Nontrivial ((twistedDerivedAction 2 q).range ⧸
      Subgroup.center (twistedDerivedAction 2 q).range) := by
  obtain ⟨g, hg⟩ := derived_image_exists_not_center q hq
  let f := twistedDerivedAction 2 q
  let π := QuotientGroup.mk' (Subgroup.center f.range)
  have hn : π (f.rangeRestrict g) ≠ 1 := by
    intro h
    exact hg ((QuotientGroup.eq_one_iff _).mp h)
  exact ⟨⟨π (f.rangeRestrict g), 1, hn⟩⟩

def twistedA2_natural_projective_equiv (q : CFSG.PrimePower) (hq : q.order ≠ 2)
    [IsSimpleGroup (CFSG.Models.TwistedA 2 q)] :
    CFSG.Models.TwistedA 2 q ≃*
      ((twistedDerivedAction 2 q).range ⧸
        Subgroup.center (twistedDerivedAction 2 q).range) := by
  have hq2 : 2 ≤ q.order := q.prime_isPrime.two_le.trans
    (Nat.le_self_pow (Nat.ne_of_gt q.exponent_pos) q.prime)
  letI := derived_projective_nontrivial q (by omega)
  exact CFSGSimpleProjectiveDescent.projectiveEquivOfSimple
    (twistedDerivedAction 2 q).rangeRestrict (twistedDerivedAction 2 q).rangeRestrict_surjective

end SymmetricSubgroupAsymptotics.CFSGTwistedA2HighestRootUnits
