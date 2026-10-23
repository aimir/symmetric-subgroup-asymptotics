import SymmetricSubgroupAsymptotics.CFSGGTwoOriginalExceptionalRepresentation
import SymmetricSubgroupAsymptotics.CFSGGTwoNaturalSevenFaithfulness
import SymmetricSubgroupAsymptotics.CFSGGTwoOriginalNaturalEquivalence
import SymmetricSubgroupAsymptotics.CFSGGeneratedActionRange
import Mathlib.FieldTheory.Finite.Basic

/-! An actual exceptional automorphism of the SAME original G2 Model in
finite characteristic three. Surjectivity comes from the four proved
root images and bijectivity of Frobenius. Finiteness and the independently
proved whole-model natural equivalence make the descended map injective.
No ordinary-G2 simplicity or presumed exceptional-isogeny map is used. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGGTwoOriginalExceptionalModel
open CFSG.Models.Chevalley CFSGSerreModelRootGeneration
open CFSGGTwoSerreMatrices CFSGGTwoSingularPointAction
open CFSGGTwoOriginalExceptionalRootCovariance CFSGGTwoOriginalExceptionalRepresentation
open CFSGGTwoOriginalNaturalEquivalence CFSGGTwoNaturalSevenFaithfulness
variable (K : Type) [Field K] [Finite K] [CharP K 3]
local notation "A" => CartanMatrix.G₂

theorem cube_surjective : Function.Surjective (fun t : K => t^3) := by
  have hi : Function.Injective (fun t : K => t^3) := frobenius_inj K 3
  exact Finite.surjective_of_injective hi

theorem action_ranges_eq : (representation K).range=(hyperplaneLinearHom K).range := by
  apply le_antisymm
  · apply CFSGGeneratedActionRange.range_le_of_generators
      (rootSet A K) (rootSet_generate A K) (representation K) (hyperplaneLinearHom K).range
    rintro g ⟨neg,i,t,rfl⟩
    exact ⟨naturalRoot K neg (exchangedNode i) (exceptionalParameter K i t),
      (representation_root K neg i t).symm⟩
  · apply CFSGGeneratedActionRange.range_le_of_generators
      (CFSGSerreQuadraticMatrix.elementaryRootSet K (rootTransvection K))
      (CFSGSerreQuadraticMatrix.elementaryRootSet_generate K (rootTransvection K))
      (hyperplaneLinearHom K) (representation K).range
    rintro g ⟨neg,i,t,rfl⟩
    fin_cases i
    · refine ⟨modelRoot A K neg 1 t,?_⟩
      exact representation_root K neg 1 t
    · obtain ⟨s,hs⟩ := cube_surjective K t
      change s^3=t at hs
      refine ⟨modelRoot A K neg 0 s,?_⟩
      have he := representation_root K neg 0 s
      change representation K (modelRoot A K neg 0 s)=
        hyperplaneLinearHom K (naturalRoot K neg 1 (s^3)) at he
      rw [hs] at he
      exact he

def sourceToNative : Model A K →* naturalGroup K :=
  ((MonoidHom.ofInjective (hyperplaneLinearHom_injective K)).symm.toMonoidHom).comp
    (((MulEquiv.subgroupCongr (action_ranges_eq K)).toMonoidHom).comp
      (representation K).rangeRestrict)

theorem sourceToNative_intertwines (g : Model A K) :
    hyperplaneLinearHom K (sourceToNative K g)=representation K g := by
  change hyperplaneLinearHom K
    ((MonoidHom.ofInjective (hyperplaneLinearHom_injective K)).symm
      (MulEquiv.subgroupCongr (action_ranges_eq K)
        ((representation K).rangeRestrict g)))=_
  rw [MonoidHom.apply_ofInjective_symm]
  rfl

theorem sourceToNative_surjective : Function.Surjective (sourceToNative K) :=
  (MonoidHom.ofInjective (hyperplaneLinearHom_injective K)).symm.surjective.comp
    ((MulEquiv.subgroupCongr (action_ranges_eq K)).surjective.comp
      (representation K).rangeRestrict_surjective)

theorem sourceToNative_root (neg : Bool) (i : Fin 2) (t : K) :
    sourceToNative K (modelRoot A K neg i t)=
      naturalRoot K neg (exchangedNode i) (exceptionalParameter K i t) := by
  apply hyperplaneLinearHom_injective K
  rw [sourceToNative_intertwines,representation_root]

def exceptionalEnd : Model A K →* Model A K :=
  (modelEquivNatural K).symm.toMonoidHom.comp (sourceToNative K)

theorem exceptionalEnd_surjective : Function.Surjective (exceptionalEnd K) :=
  (modelEquivNatural K).symm.surjective.comp (sourceToNative_surjective K)

theorem exceptionalEnd_injective : Function.Injective (exceptionalEnd K) := by
  letI : Finite (Model A K) := Finite.of_injective (modelEquivNatural K)
    (modelEquivNatural K).injective
  exact Finite.injective_iff_surjective.mpr (exceptionalEnd_surjective K)

def exceptionalModelEquiv : MulAut (Model A K) :=
  MulEquiv.ofBijective (exceptionalEnd K)
    ⟨exceptionalEnd_injective K,exceptionalEnd_surjective K⟩

theorem exceptionalModelEquiv_root (neg : Bool) (i : Fin 2) (t : K) :
    exceptionalModelEquiv K (modelRoot A K neg i t)=
      modelRoot A K neg (exchangedNode i) (exceptionalParameter K i t) := by
  change (modelEquivNatural K).symm (sourceToNative K (modelRoot A K neg i t))=_
  rw [sourceToNative_root]
  apply (modelEquivNatural K).injective
  rw [(modelEquivNatural K).apply_symm_apply,modelEquivNatural_root]

theorem exceptionalModelEquiv_twice_root (neg : Bool) (i : Fin 2) (t : K) :
    exceptionalModelEquiv K (exceptionalModelEquiv K (modelRoot A K neg i t))=
      modelRoot A K neg i (t^3) := by
  rw [exceptionalModelEquiv_root,exceptionalModelEquiv_root]
  fin_cases i <;> rfl

end SymmetricSubgroupAsymptotics.CFSGGTwoOriginalExceptionalModel
