import SymmetricSubgroupAsymptotics.CFSGReeFFourBinaryCentralWordProperties
import SymmetricSubgroupAsymptotics.CFSGTitsPairStabilizerCentres

/-! The actual nonidentity Tits positive-centre element and its original
whole-word value, transported through the checked injective full-centre
quotient on this SAME positive-derived subgroup. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGTitsPositiveCentralRoot
open CFSGReeFFourBinaryCentralWordProperties CFSGReeFFourBinaryPositiveCentralWord
open CFSGReeFFourBinarySylowNormalizerSolvable CFSGTitsPairStabilizerCentres
open CFSGTitsAmbientPairAlignment CFSGReeFFourDerivedAmbientHom
open CFSGReeFFourAllParameterDerivedPositive CFSGReeFFourOriginalPositiveSylow

private theorem positive_range_eq_sylow : titsPositiveHom.range=
    (titsPositiveSylow : Subgroup CFSG.Models.Tits) := by
  have hr : titsPositiveHom.range=(derivedPositive 0).map (derivedReeHom 0) := by
    ext x
    constructor
    · rintro ⟨y,rfl⟩
      exact ⟨y.val,y.property,rfl⟩
    · rintro ⟨y,hy,rfl⟩
      exact ⟨⟨y,hy⟩,rfl⟩
  exact hr.trans titsPositiveSylow_coe.symm

def positiveEquiv : derivedPositive 0≃*titsPositiveSylow :=
  (MonoidHom.ofInjective titsPositiveHom_injective).trans
    (MulEquiv.subgroupCongr positive_range_eq_sylow)

def positiveCentre : Subgroup.center titsPositiveSylow :=
  Subgroup.centerCongr positiveEquiv centralSource

def positiveRoot : CFSG.Models.Tits := positiveCentre.val.val

theorem positiveRoot_value : positiveRoot=
    derivedReeHom 0 ⟨centralWord,centralWord_mem_derived⟩ := by
  change derivedReeHom 0 centralSource.val.val=
    derivedReeHom 0 ⟨centralWord,centralWord_mem_derived⟩
  exact congrArg (derivedReeHom 0) (Subtype.ext centralSource_value)

theorem positiveCentre_ne_one : positiveCentre≠1 := by
  intro h
  let e := Subgroup.centerCongr positiveEquiv
  have he : e centralSource=e 1 := h.trans (map_one e).symm
  exact centralSource_ne_one (e.injective he)

theorem positiveRoot_ne_one : positiveRoot≠1 := by
  intro h
  exact positiveCentre_ne_one (Subtype.ext (Subtype.ext h))

theorem pairStabilizer_fixes_positiveRoot (f : pairStabilizer) :
    f.val positiveRoot=positiveRoot :=
  fixes_positive_center f positiveCentre

end SymmetricSubgroupAsymptotics.CFSGTitsPositiveCentralRoot
