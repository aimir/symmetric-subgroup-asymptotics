import SymmetricSubgroupAsymptotics.CFSGTrialityGeckHighestWeylMiddleGrade
import SymmetricSubgroupAsymptotics.CFSGTrialityGeckMiddleNormOrbitWords
import SymmetricSubgroupAsymptotics.CFSGTrialityGeckShortSectionCentralizer
import SymmetricSubgroupAsymptotics.CFSGTrialityGeckSignedSectionMembership
import SymmetricSubgroupAsymptotics.CFSGTrialityGeckFixedShortComplementFactor

/-! Exact RAW fixed-positive short-axis recognition from the two fixed
highest root lines. Their actual Weyl word reverses middle grading, so
the middle radical contributes no centralizer element. The existing
fixed complement factorization supplies the literal short orbit word.
Transport of projective commutation to raw commutation is separate. -/
set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGTrialityGeckShortAxisCentralizer
open CFSGTrialityGeckDiagramCovariance CFSGTrialityGeckMiddleRadicalQuotient
open CFSGTrialityGeckMiddleRadicalCardinality CFSGTrialityGeckHighestWeylMiddleGrade
open CFSGTrialityGeckMiddleNormOrbitWords CFSGTrialityGeckFixedRootWords
open CFSGTrialityGeckFixedRootSections CFSGTrialityGeckShortOrbitCommutator
open CFSGTrialityGeckShortSectionCentralizer CFSGTrialityGeckLongShortOrthogonality
open CFSGTrialityGeckSignedSectionMembership
open CFSGTrialityGeckFixedPositiveRaw CFSGTrialityGeckFixedWordSimpleSigns
open CFSGTrialityGeckFixedShortComplementFactor CFSGTrialityGeckMatrixTwist
open CFSGTrialityFixedField CFSGSerreOrdinaryTwists
local instance : DecidableEq (CFSGNormTwoRootPairing.Roots (CartanMatrix.D 4)) := Classical.decEq _
local instance : DecidableEq GeckIndex := inferInstance

def highestPairSet (q : CFSG.PrimePower) : Set (Raw (q.Extension 3)) :=
  Set.range (fun b : fixedField q => longSection (q.Extension 3) 2 false b.val) ∪
    Set.range (fun b : fixedField q => longSection (q.Extension 3) 2 true b.val)

def highestPairCentralizer (q : CFSG.PrimePower) : Subgroup (Raw (q.Extension 3)) :=
  Subgroup.centralizer (highestPairSet q)

theorem middle_highestPairCentralizer_eq_one (q : CFSG.PrimePower) (u : Raw (q.Extension 3))
    (hu : u ∈ middleRadical (q.Extension 3)) (hc : u ∈ highestPairCentralizer q) : u = 1 := by
  have hpositive : Commute u (longSection (q.Extension 3) 2 false 1) :=
    (hc _ (Or.inl ⟨(1 : fixedField q),rfl⟩)).symm
  have hnegative : Commute u (longSection (q.Extension 3) 2 true (-1)) :=
    (hc _ (Or.inr ⟨(-1 : fixedField q),rfl⟩)).symm
  apply middle_commuting_highestWeyl_eq_one (q.Extension 3) u hu
  rw [highestWeyl_root_word]
  exact (hpositive.mul_right hnegative).mul_right hpositive

private theorem shortOrbit_commutes_signedLong (q : CFSG.PrimePower) (neg : Bool)
    (t : q.Extension 3) (b : fixedField q) :
    Commute (shortOrbit (q.Extension 3) (definingFieldAutomorphism q 3) false t)
      (longSection (q.Extension 3) 2 neg b.val) := by
  have h := shortSection_commute (q.Extension 3) (definingFieldAutomorphism q 3)
    neg 2 t (longSection (q.Extension 3) 2 neg b.val)
    (signedLongSection_mem_root (q.Extension 3) neg 2 b.val)
  have he : shortSection (q.Extension 3) (definingFieldAutomorphism q 3)
      (centralizerShort 2) false t =
      shortOrbit (q.Extension 3) (definingFieldAutomorphism q 3) false t := by
    have hzero : centralizerShort (2 : Fin 3) = 0 := rfl
    rw [hzero]
    change 1 * shortOrbit (q.Extension 3) (definingFieldAutomorphism q 3) false t * 1⁻¹ = _
    simp only [inv_one,one_mul,mul_one]
  rw [he] at h
  exact h

theorem shortOrbit_mem_highestPairCentralizer (q : CFSG.PrimePower) (t : q.Extension 3) :
    shortOrbit (q.Extension 3) (definingFieldAutomorphism q 3) false t ∈ highestPairCentralizer q := by
  intro z hz
  rcases hz with ⟨b,rfl⟩ | ⟨b,rfl⟩
  · exact (shortOrbit_commutes_signedLong q false t b).eq.symm
  · exact (shortOrbit_commutes_signedLong q true t b).eq.symm

theorem fixedPositive_centralizer_iff (q : CFSG.PrimePower) (u : Raw (q.Extension 3)) :
    u ∈ fixedPositiveRaw q ⊓ highestPairCentralizer q ↔
      ∃ t : q.Extension 3, u = shortOrbit (q.Extension 3) (definingFieldAutomorphism q 3) false t := by
  constructor
  · rintro ⟨hu,hc⟩
    have huf := (mem_fixedPositiveRaw_iff q u).mp hu
    obtain ⟨c,hcR,t,_,_,he⟩ := exists_fixed_positive_short_factor _ _ u huf.1 huf.2
    have hcC : c ∈ highestPairCentralizer q := by
      have hec : c = u * (shortOrbit (q.Extension 3) (definingFieldAutomorphism q 3) false t)⁻¹ := by
        rw [he]
        group
      rw [hec]
      exact (highestPairCentralizer q).mul_mem hc
        ((highestPairCentralizer q).inv_mem (shortOrbit_mem_highestPairCentralizer q t))
    have hcMiddle : c ∈ middleRadical (q.Extension 3) := by rwa [middleRadical_eq_shortComplement]
    have hc1 := middle_highestPairCentralizer_eq_one q c hcMiddle hcC
    refine ⟨t,?_⟩
    simpa only [hc1,one_mul] using he
  · rintro ⟨t,rfl⟩
    exact ⟨shortOrbit_mem_fixedPositiveRaw q t,shortOrbit_mem_highestPairCentralizer q t⟩

end SymmetricSubgroupAsymptotics.CFSGTrialityGeckShortAxisCentralizer
