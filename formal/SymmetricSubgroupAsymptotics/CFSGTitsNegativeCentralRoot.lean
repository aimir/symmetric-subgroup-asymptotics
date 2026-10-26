import SymmetricSubgroupAsymptotics.CFSGTitsPositiveCentralRoot
import SymmetricSubgroupAsymptotics.SubgroupActionIntersectionTransport

/-! The actual ambient opposition transports the SAME positive centre
through the full quotient to the literal negative Sylow centre. This is
an existing ambient action, not a lift of any target automorphism. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGTitsNegativeCentralRoot
open CFSGTitsPositiveCentralRoot CFSGTitsAmbientPairAlignment
open CFSGTitsPairStabilizerCentres CFSGReeFFourBinarySylowNormalizerSolvable
open CFSGReeFFourAmbientCentralQuotientAction CFSGReeFFourDerivedAmbientHom
open CFSGReeFFourFixedModelEquivalence CFSGReeFFourFixedPositiveFamilies
open CFSGReeFFourOppositionFixedPositiveNegative CFSGReeFFourOriginalPositiveSylow
private abbrev D := commutator (originalModelFixed 0)

theorem positive_map_opposition :
    (titsPositiveSylow : Subgroup CFSG.Models.Tits).map
      (ambientAction 0 (oppositionFixed 0)).toMonoidHom=
        (titsNegativeSylow : Subgroup CFSG.Models.Tits) := by
  have hs : (derivedPositive 0).map (MulAut.conjNormal (oppositionFixed 0)).toMonoidHom=
      (fixedNegative 0).comap D.subtype := by
    have h := SubgroupActionIntersectionTransport.normal_comap_conjugate
      D (fixedPositive 0) (oppositionFixed 0)
    rw [fixed_positive_image_eq_fixed_negative] at h
    exact h.symm
  rw [titsPositiveSylow_coe,←ambientAction_map,hs]
  exact titsNegativeSylow_coe.symm

def oppositionEquiv : titsPositiveSylow≃*titsNegativeSylow :=
  ((ambientAction 0 (oppositionFixed 0)).subgroupMap
    (titsPositiveSylow : Subgroup CFSG.Models.Tits)).trans
      (MulEquiv.subgroupCongr positive_map_opposition)

def negativeCentre : Subgroup.center titsNegativeSylow :=
  Subgroup.centerCongr oppositionEquiv positiveCentre

def negativeRoot : CFSG.Models.Tits := negativeCentre.val.val

theorem negativeRoot_value : negativeRoot=ambientAction 0 (oppositionFixed 0) positiveRoot := rfl

theorem negativeRoot_ne_one : negativeRoot≠1 := by
  rw [negativeRoot_value]
  intro h
  exact positiveRoot_ne_one ((ambientAction 0 (oppositionFixed 0)).injective
    (h.trans (map_one (ambientAction 0 (oppositionFixed 0))).symm))

theorem pairStabilizer_fixes_negativeRoot (f : pairStabilizer) :
    f.val negativeRoot=negativeRoot :=
  fixes_negative_center f negativeCentre

end SymmetricSubgroupAsymptotics.CFSGTitsNegativeCentralRoot
