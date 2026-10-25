import SymmetricSubgroupAsymptotics.AutomorphismFixedOrderTwoCentre
import SymmetricSubgroupAsymptotics.CFSGReeFFourBinaryPositiveCentre
import SymmetricSubgroupAsymptotics.CFSGTitsAmbientPairAlignment

/-! The literal opposed-Sylow pair stabilizer fixes both subgroup centres
pointwise. This is intrinsic subgroup information, not a bound on the
pair stabilizer and not an extension of its automorphisms to an overgroup. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGTitsPairStabilizerCentres
open CFSGReeFFourBinaryPositiveCentre CFSGTitsAmbientPairAlignment
open CFSGReeFFourBinarySylowNormalizerSolvable
open CFSGReeFFourFixedModelEquivalence CFSGReeFFourOriginalPositiveSylow
open CFSGReeFFourDerivedAmbientHom
local instance : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩

private instance derivedFinite : Finite (commutator (originalModelFixed 0)) :=
  Finite.of_injective (derivedAmbientHom 0) (derivedAmbientHom_injective 0)
private instance titsFinite : Finite CFSG.Models.Tits :=
  Finite.of_surjective (derivedReeHom 0) (derivedReeHom_surjective 0)

theorem tits_negative_sylow_center_card_eq_two :
    Nat.card (Subgroup.center titsNegativeSylow)=2 := by
  have he := Nat.card_congr
    (Subgroup.centerCongr (Sylow.equiv titsNegativeSylow titsPositiveSylow)).toEquiv
  exact he.trans tits_positive_sylow_center_card_eq_two

theorem fixes_positive_center (f : pairStabilizer)
    (z : Subgroup.center titsPositiveSylow) :
    f.val (z.val : CFSG.Models.Tits)=(z.val : CFSG.Models.Tits) := by
  exact AutomorphismFixedOrderTwoCentre.fixes_subgroup_center
    (titsPositiveSylow : Subgroup CFSG.Models.Tits) f.val
    ((mem_pairStabilizer f.val).mp f.property).1
    tits_positive_sylow_center_card_eq_two z

theorem fixes_negative_center (f : pairStabilizer)
    (z : Subgroup.center titsNegativeSylow) :
    f.val (z.val : CFSG.Models.Tits)=(z.val : CFSG.Models.Tits) := by
  exact AutomorphismFixedOrderTwoCentre.fixes_subgroup_center
    (titsNegativeSylow : Subgroup CFSG.Models.Tits) f.val
    ((mem_pairStabilizer f.val).mp f.property).2
    tits_negative_sylow_center_card_eq_two z

end SymmetricSubgroupAsymptotics.CFSGTitsPairStabilizerCentres
