import SymmetricSubgroupAsymptotics.CFSGReeFFourBinaryExactPositiveNormalizer
import SymmetricSubgroupAsymptotics.CFSGReeFFourBinarySylowNormalizerSolvable

/-! The exact normalizer descends to the SAME actual derived positive
subgroup and through the FULL central quotient defining Tits. The Sylow
normalizer is lifted through the actual surjection, not through a lifted
automorphism or a chosen model recognition. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGTitsPositiveSelfNormalizer
open CFSGReeFFourBinaryExactPositiveNormalizer CFSGReeFFourBinarySylowNormalizerSolvable
open CFSGReeFFourBinaryDerivedNormalizerParabolic CFSGReeFFourDerivedAmbientHom
open CFSGReeFFourFixedModelEquivalence CFSGReeFFourAllParameterDerivedPositive
open CFSGReeFFourOriginalPositiveSylow
local instance : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
private abbrev D := commutator (originalModelFixed 0)
private instance derivedFinite : Finite D :=
  Finite.of_injective (derivedAmbientHom 0) (derivedAmbientHom_injective 0)

private theorem positive_map : (derivedPositive 0).map D.subtype=ambientDerivedPositive 0 := by
  ext x
  constructor
  · rintro ⟨y,hy,rfl⟩
    exact ⟨hy,y.property⟩
  · intro hx
    exact ⟨⟨x,hx.2⟩,hx.1,rfl⟩

theorem derivedPositive_normalizer_eq :
    Subgroup.normalizer (derivedPositive 0 : Set D)=derivedPositive 0 := by
  apply le_antisymm
  · intro x hx
    have hh := (derivedPositive 0).le_normalizer_map D.subtype
      (show (x : originalModelFixed 0)∈
        (Subgroup.normalizer (derivedPositive 0 : Set D)).map D.subtype from ⟨x,hx,rfl⟩)
    rw [positive_map,ambientDerivedPositive_normalizer_eq_positive] at hh
    exact hh
  · exact (derivedPositive 0).le_normalizer

theorem positiveSylow_normalizer_eq :
    Subgroup.normalizer (positiveSylow 0 : Set D)=(positiveSylow 0 : Subgroup D) := by
  have hP : (positiveSylow 0 : Subgroup D)=derivedPositive 0 := positiveSylow_coe 0
  have hN : Subgroup.normalizer (positiveSylow 0 : Set D)=
      Subgroup.normalizer (derivedPositive 0 : Set D) :=
    congrArg (fun S : Subgroup D => Subgroup.normalizer (S : Set D)) hP
  exact hN.trans (derivedPositive_normalizer_eq.trans hP.symm)

theorem titsPositiveSylow_normalizer_eq :
    Subgroup.normalizer (titsPositiveSylow : Set CFSG.Models.Tits)=
      (titsPositiveSylow : Subgroup CFSG.Models.Tits) := by
  apply le_antisymm
  · intro x hx
    have hmap : (titsPositiveSylow : Subgroup CFSG.Models.Tits)=
        (positiveSylow 0 : Subgroup D).map (derivedReeHom 0) := rfl
    have hx' : x∈Subgroup.normalizer
        ((positiveSylow 0 : Subgroup D).map (derivedReeHom 0) : Set CFSG.Models.Tits) := by
      simpa only [hmap] using hx
    obtain ⟨y,hy,he⟩ := SylowActualNormalizerLift.exists_lift
      (derivedReeHom 0) (derivedReeHom_surjective 0) (positiveSylow 0) x hx'
    rw [positiveSylow_normalizer_eq] at hy
    rw [hmap]
    exact ⟨y,hy,he⟩
  · exact (titsPositiveSylow : Subgroup CFSG.Models.Tits).le_normalizer

end SymmetricSubgroupAsymptotics.CFSGTitsPositiveSelfNormalizer
