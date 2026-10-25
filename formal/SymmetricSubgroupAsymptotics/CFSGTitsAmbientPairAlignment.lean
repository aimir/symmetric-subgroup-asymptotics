import SymmetricSubgroupAsymptotics.CentralKernelSylowPairLift
import SymmetricSubgroupAsymptotics.SubgroupQuotientActionTransport
import SymmetricSubgroupAsymptotics.CFSGReeFFourAmbientCentralQuotientAction
import SymmetricSubgroupAsymptotics.CFSGReeFFourBinaryDerivedPairAlignment
import SymmetricSubgroupAsymptotics.CFSGReeFFourBinarySylowNormalizerSolvable
import SymmetricSubgroupAsymptotics.CFSGSubgroupFamilyStabilizer

/-! Actual Tits Sylow-pair alignment by the FULL fixed-group action.
We lift two Sylow subgroups separately through the full derived-centre
quotient; we do not lift their automorphism. The literal pair stabilizer
and its ambient normalization cover are conclusions, not rigidity or
outer-order assumptions. The normalizer remains in G rather than D. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGTitsAmbientPairAlignment
open CFSGReeFFourFixedModelEquivalence CFSGReeFFourDerivedAmbientHom
open CFSGReeFFourAllParameterDerivedPositive CFSGReeFFourOriginalPositiveSylow
open CFSGReeFFourBinarySylowNormalizerSolvable CFSGReeFFourBinaryDerivedPairAlignment
open CFSGReeFFourAmbientCentralQuotientAction CFSGReeFFourFixedPositiveFamilies
open CFSGReeFFourOppositionFixedPositiveNegative
open CFSGSubgroupFamilyStabilizer
local instance : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
private abbrev D := commutator (originalModelFixed 0)
private instance derivedFinite : Finite D :=
  Finite.of_injective (derivedAmbientHom 0) (derivedAmbientHom_injective 0)

theorem positive_quotient_injective :
    Function.Injective ((derivedReeHom 0).comp (positiveSylow 0 : Subgroup D).subtype) := by
  intro x y he
  apply CFSGDisjointSylowProjectiveCardinality.central_quotient_injective
    (positiveSylow 0) (negativeSylow 0) (opposite_inf 0)
  exact (originalReeEquiv 0).symm.injective he

def titsNegativeSylow : Sylow 2 CFSG.Models.Tits :=
  (negativeSylow 0).mapSurjective (f := derivedReeHom 0) (derivedReeHom_surjective 0)

theorem titsNegativeSylow_coe :
    (titsNegativeSylow : Subgroup CFSG.Models.Tits) =
      ((fixedNegative 0).comap D.subtype).map (derivedReeHom 0) := by
  change (negativeSylow 0 : Subgroup D).map (derivedReeHom 0) = _
  rw [negativeSylow_eq_comap]

theorem quotient_opposite_inf :
    (titsPositiveSylow : Subgroup CFSG.Models.Tits) ⊓
      (titsNegativeSylow : Subgroup CFSG.Models.Tits) = ⊥ := by
  change ((positiveSylow 0 : Subgroup D).map (derivedReeHom 0)) ⊓
    ((negativeSylow 0 : Subgroup D).map (derivedReeHom 0)) = ⊥
  exact CFSGCentralKernelPElements.disjoint_map (derivedReeHom 0) (positiveSylow 0)
    positive_quotient_injective (le_of_eq (derivedReeHom_ker 0))
    (positiveSylow 0 : Subgroup D) (negativeSylow 0 : Subgroup D)
    (positiveSylow 0).isPGroup' (negativeSylow 0).isPGroup' (opposite_inf 0)

theorem exists_ambient_conjugating_pair
    (A B : Sylow 2 CFSG.Models.Tits)
    (hAB : (A : Subgroup CFSG.Models.Tits) ⊓ (B : Subgroup CFSG.Models.Tits) = ⊥) :
    ∃ g : originalModelFixed 0,
      (A : Subgroup CFSG.Models.Tits).map (ambientAction 0 g).toMonoidHom =
        (titsPositiveSylow : Subgroup CFSG.Models.Tits) ∧
      (B : Subgroup CFSG.Models.Tits).map (ambientAction 0 g).toMonoidHom =
        (titsNegativeSylow : Subgroup CFSG.Models.Tits) := by
  obtain ⟨R, S, hR, hS, hRS⟩ := CentralKernelSylowPairLift.exists_lift_pair
    (derivedReeHom 0) (derivedReeHom_surjective 0) (positiveSylow 0)
    positive_quotient_injective (le_of_eq (derivedReeHom_ker 0)) A B hAB
  obtain ⟨g, hgR, hgS⟩ :=
    CFSGReeFFourBinaryDerivedPairAlignment.exists_ambient_conjugating_pair R S hRS
  refine ⟨g, ?_, ?_⟩
  · exact SubgroupQuotientActionTransport.map_alignment
      (G := D) (H := CFSG.Models.Tits)
      (derivedReeHom 0) (MulAut.conjNormal g) (ambientAction 0 g)
      (ambientAction_apply 0 g)
      (R : Subgroup D) (derivedPositive 0)
      (A : Subgroup CFSG.Models.Tits) (titsPositiveSylow : Subgroup CFSG.Models.Tits)
      hR titsPositiveSylow_coe.symm hgR
  · exact SubgroupQuotientActionTransport.map_alignment
      (G := D) (H := CFSG.Models.Tits)
      (derivedReeHom 0) (MulAut.conjNormal g) (ambientAction 0 g)
      (ambientAction_apply 0 g)
      (S : Subgroup D) ((fixedNegative 0).comap D.subtype)
      (B : Subgroup CFSG.Models.Tits) (titsNegativeSylow : Subgroup CFSG.Models.Tits)
      hS titsNegativeSylow_coe.symm hgS

theorem exists_ambient_fix_pair (f : MulAut CFSG.Models.Tits) :
    ∃ g : originalModelFixed 0,
      (titsPositiveSylow : Subgroup CFSG.Models.Tits).map
        (ambientAction 0 g * f).toMonoidHom =
          (titsPositiveSylow : Subgroup CFSG.Models.Tits) ∧
      (titsNegativeSylow : Subgroup CFSG.Models.Tits).map
        (ambientAction 0 g * f).toMonoidHom =
          (titsNegativeSylow : Subgroup CFSG.Models.Tits) := by
  let A : Sylow 2 CFSG.Models.Tits :=
    titsPositiveSylow.mapSurjective (f := f.toMonoidHom) f.surjective
  let B : Sylow 2 CFSG.Models.Tits :=
    titsNegativeSylow.mapSurjective (f := f.toMonoidHom) f.surjective
  have hAB : (A : Subgroup CFSG.Models.Tits) ⊓ (B : Subgroup CFSG.Models.Tits) = ⊥ := by
    change (titsPositiveSylow : Subgroup CFSG.Models.Tits).map f.toMonoidHom ⊓
      (titsNegativeSylow : Subgroup CFSG.Models.Tits).map f.toMonoidHom = ⊥
    rw [← Subgroup.map_inf _ _ f.toMonoidHom f.injective,
      quotient_opposite_inf, Subgroup.map_bot]
  obtain ⟨g, hA, hB⟩ := exists_ambient_conjugating_pair A B hAB
  refine ⟨g, ?_, ?_⟩
  · change (titsPositiveSylow : Subgroup CFSG.Models.Tits).map
      ((ambientAction 0 g).toMonoidHom.comp f.toMonoidHom) = _
    rw [← Subgroup.map_map]
    exact hA
  · change (titsNegativeSylow : Subgroup CFSG.Models.Tits).map
      ((ambientAction 0 g).toMonoidHom.comp f.toMonoidHom) = _
    rw [← Subgroup.map_map]
    exact hB

def pairStabilizer : Subgroup (MulAut CFSG.Models.Tits) :=
  familyStabilizer (fun b : Bool => if b then
    (titsNegativeSylow : Subgroup CFSG.Models.Tits) else
    (titsPositiveSylow : Subgroup CFSG.Models.Tits))

theorem mem_pairStabilizer (f : MulAut CFSG.Models.Tits) :
    f ∈ pairStabilizer ↔
      (titsPositiveSylow : Subgroup CFSG.Models.Tits).map f.toMonoidHom =
        (titsPositiveSylow : Subgroup CFSG.Models.Tits) ∧
      (titsNegativeSylow : Subgroup CFSG.Models.Tits).map f.toMonoidHom =
        (titsNegativeSylow : Subgroup CFSG.Models.Tits) := by
  change (∀ b : Bool, ((if b then
    (titsNegativeSylow : Subgroup CFSG.Models.Tits) else
    (titsPositiveSylow : Subgroup CFSG.Models.Tits))).map f.toMonoidHom = _) ↔ _
  constructor
  · intro h
    exact ⟨h false, h true⟩
  · rintro ⟨hP, hQ⟩ b
    cases b
    · exact hP
    · exact hQ

theorem ambient_normalization_cover (f : MulAut CFSG.Models.Tits) :
    ∃ g : originalModelFixed 0, ambientAction 0 g * f ∈ pairStabilizer := by
  obtain ⟨g, hP, hQ⟩ := exists_ambient_fix_pair f
  exact ⟨g, (mem_pairStabilizer _).mpr ⟨hP, hQ⟩⟩

end SymmetricSubgroupAsymptotics.CFSGTitsAmbientPairAlignment
