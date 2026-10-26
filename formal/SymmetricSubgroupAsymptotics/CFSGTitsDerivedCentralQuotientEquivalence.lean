import SymmetricSubgroupAsymptotics.CentralKernelSelfNormalizerInjectivity
import SymmetricSubgroupAsymptotics.CFSGTitsPositiveSelfNormalizer
import SymmetricSubgroupAsymptotics.CFSGTitsAmbientPairAlignment

/-! The FULL binary derived-centre quotient is actually injective.
This follows from the checked exact Sylow normalizer and the already
proved quotient injectivity on that SAME Sylow, so no full-centre
vanishing or automorphism-lifting assumption is introduced. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGTitsDerivedCentralQuotientEquivalence
open CFSGTitsPositiveSelfNormalizer CFSGTitsAmbientPairAlignment
open CFSGReeFFourOriginalPositiveSylow CFSGReeFFourFixedModelEquivalence
open CFSGReeFFourAmbientCentralQuotientAction CFSGReeFFourAllParameterDerivedPositive
private abbrev D := commutator (originalModelFixed 0)

theorem derivedReeHom_injective : Function.Injective (derivedReeHom 0) :=
  CentralKernelSelfNormalizerInjectivity.injective (derivedReeHom 0)
    (positiveSylow 0 : Subgroup D) positive_quotient_injective
    (le_of_eq (derivedReeHom_ker 0)) positiveSylow_normalizer_eq

theorem derived_center_eq_bot : Subgroup.center D=⊥ :=
  (derivedReeHom_ker 0).symm.trans
    ((derivedReeHom 0).ker_eq_bot_iff.mpr derivedReeHom_injective)

def derivedEquivTits : D≃*CFSG.Models.Tits :=
  MulEquiv.ofBijective (derivedReeHom 0)
    ⟨derivedReeHom_injective,derivedReeHom_surjective 0⟩

theorem derivedEquivTits_apply (d : D) : derivedEquivTits d=derivedReeHom 0 d := rfl

end SymmetricSubgroupAsymptotics.CFSGTitsDerivedCentralQuotientEquivalence
