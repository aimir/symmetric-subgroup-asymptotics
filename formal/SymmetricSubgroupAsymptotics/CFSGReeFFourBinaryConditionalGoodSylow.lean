import SymmetricSubgroupAsymptotics.CFSGReeFFourBinaryDerivedOppositeGeneration
import SymmetricSubgroupAsymptotics.CFSGReeFFourBinarySylowNormalizerSolvable
import SymmetricSubgroupAsymptotics.CFSGGoodSylowOfTwoPSubgroups
import SymmetricSubgroupAsymptotics.CFSGGoodSylowPrimeSurjective

/-! Actual good-Sylow data for the original binary derived fixed group
and its FULL derived-centre quotient. The sole conditional input is the
original outer involution's derived membership. Generation is proved by
the same actual positive/negative Sylows; an internal conjugating element
is obtained by Sylow conjugacy, never by asserting opposition lies in D. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGReeFFourBinaryConditionalGoodSylow
open CFSGReeFFourFixedModelEquivalence CFSGReeFFourOuterThreeWord
open CFSGReeFFourDerivedAmbientHom CFSGReeFFourAllParameterDerivedPositive
open CFSGReeFFourBinaryDerivedOppositeGeneration CFSGReeFFourOriginalPositiveSylow
open CFSGReeFFourBinarySylowNormalizerSolvable CFSGReduction
local instance : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
private abbrev D := commutator (originalModelFixed 0)
private instance derived_finite : Finite D :=
  Finite.of_injective (derivedAmbientHom 0) (derivedAmbientHom_injective 0)

/-- Same original derived group, actual Sylows, soluble normalizer and
an internal Sylow-conjugacy witness. -/
theorem derived_goodSylowPrime (hxD : outerInvolution 0 ∈ D) : GoodSylowPrime D 2 := by
  have hsol : ∃ Q : Sylow 2 D,
      IsSolvable (Subgroup.normalizer (Q : Set D)) := by
    refine ⟨positiveSylow 0, ?_⟩
    change IsSolvable (Subgroup.normalizer ((positiveSylow 0 : Subgroup D) : Set D))
    rw [positiveSylow_coe]
    exact derivedPositive_normalizer_solvable
  exact goodSylowPrime_of_two_p_subgroups_and_exists_soluble_normalizer
    (positiveSylow 0 : Subgroup D) (negativeSylow 0 : Subgroup D)
    (positiveSylow 0).isPGroup' (negativeSylow 0).isPGroup'
    (positive_sup_negative_eq_top hxD) hsol

/-- Surjective transport retains the FULL central quotient defining
the actual original Tits model; no centre is silently discarded. -/
theorem tits_goodSylowPrime (hxD : outerInvolution 0 ∈ D) :
    GoodSylowPrime CFSG.Models.Tits 2 :=
  goodSylowPrime_surjective (derivedReeHom 0) (derivedReeHom_surjective 0)
    (derived_goodSylowPrime hxD)

end SymmetricSubgroupAsymptotics.CFSGReeFFourBinaryConditionalGoodSylow
