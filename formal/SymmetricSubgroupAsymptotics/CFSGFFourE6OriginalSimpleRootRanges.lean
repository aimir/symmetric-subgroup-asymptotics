import SymmetricSubgroupAsymptotics.CFSGFFourE6OriginalRootIntersection
import SymmetricSubgroupAsymptotics.CFSGFFourE6OriginalSimpleParameters
import SymmetricSubgroupAsymptotics.CFSGE6GeckNegativeOrbitRootGroups

/-! Complete intrinsic singleton/paired root subgroups equal the ranges
of the actual native F4 simple parameters. Both signs are covered; no
root-length preservation is inferred. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics.CFSGFFourE6OriginalSimpleRootRanges
open CFSGFFourE6OriginalSimpleParameters CFSGFFourE6OriginalRootIntersection
open CFSGFFourE6GeneratedOriginalProjection CFSGFFourE6OriginalOppositeAlignment
open CFSGE6GeckFixedOrbitRootGroups CFSGE6GeckNegativeOrbitRootGroups
open CFSGE6GeckFixedSimpleParameters CFSGTwistedE6GeckRelativeRootGenerated
open CFSGE6GeckGeneratedRootIntersection CFSG.Models.Chevalley

theorem foldedFixedHom_paired (K : Type) [Field K] (neg : Bool) (j : Fin 2) :
    foldedFixedHom K neg (pairedOrbit j)=pairedFixedHom K (RingEquiv.refl K) (fun _ => rfl) neg j := by
  apply MonoidHom.ext
  intro a
  apply Subtype.ext
  rw [foldedFixedHom_val_as_raw]
  fin_cases j <;> rfl

theorem singleton_fixed_range (K : Type) [Field K] (neg : Bool) (j : Fin 2) :
    (singletonFixedHom K (RingEquiv.refl K) neg j).range=
      (foldedFixedHom K neg (singletonOrbit j)).range := by
  ext x
  constructor
  · rintro ⟨a,rfl⟩
    refine ⟨Multiplicative.ofAdd (a.toAdd : K),?_⟩
    apply Subtype.ext
    rw [foldedFixedHom_val_as_raw,singletonFixedHom_val]
    fin_cases j <;> rfl
  · rintro ⟨a,rfl⟩
    refine ⟨Multiplicative.ofAdd (⟨a.toAdd,rfl⟩ : fixedCoefficient K (RingEquiv.refl K)),?_⟩
    apply Subtype.ext
    rw [foldedFixedHom_val_as_raw,singletonFixedHom_val]
    fin_cases j <;> rfl

theorem fixedOrbitPositive_native_range (K : Type) [Field K] (a : Fin 4) :
    fixedOrbitPositive K (RingEquiv.refl K) a=(foldedFixedHom K false a).range := by
  fin_cases a
  · exact (fixedOrbitPositive_paired K (RingEquiv.refl K) (fun _ => rfl) 0).trans
      (congrArg MonoidHom.range (foldedFixedHom_paired K false 0).symm)
  · exact (fixedOrbitPositive_paired K (RingEquiv.refl K) (fun _ => rfl) 1).trans
      (congrArg MonoidHom.range (foldedFixedHom_paired K false 1).symm)
  · exact (fixedOrbitPositive_singleton K (RingEquiv.refl K) 1).trans (singleton_fixed_range K false 1)
  · exact (fixedOrbitPositive_singleton K (RingEquiv.refl K) 0).trans (singleton_fixed_range K false 0)

theorem fixedOrbitNegative_native_range (K : Type) [Field K] (a : Fin 4) :
    fixedOrbitNegative K (RingEquiv.refl K) a=(foldedFixedHom K true a).range := by
  fin_cases a
  · exact (fixedOrbitNegative_paired K (RingEquiv.refl K) (fun _ => rfl) 0).trans
      (congrArg MonoidHom.range (foldedFixedHom_paired K true 0).symm)
  · exact (fixedOrbitNegative_paired K (RingEquiv.refl K) (fun _ => rfl) 1).trans
      (congrArg MonoidHom.range (foldedFixedHom_paired K true 1).symm)
  · exact (fixedOrbitNegative_singleton K (RingEquiv.refl K) 1).trans (singleton_fixed_range K true 1)
  · exact (fixedOrbitNegative_singleton K (RingEquiv.refl K) 0).trans (singleton_fixed_range K true 0)

theorem originalOrbitRoot_eq_simple_range (K : Type) [Field K] [Finite K]
    [IsSimpleGroup (Projective CartanMatrix.F₄ K)] (a : Fin 4) :
    originalOrbitRoot K a=(originalSimpleHom K false a).range := by
  rw [originalOrbitRoot,orbitRootGenerated,Subgroup.map_map]
  change (fixedOrbitPositive K (RingEquiv.refl K) a).map (signedFixedToOriginal K false)=_
  rw [fixedOrbitPositive_native_range,MonoidHom.map_range]
  rfl

theorem negative_orbit_image_eq_simple_range (K : Type) [Field K] [Finite K]
    [IsSimpleGroup (Projective CartanMatrix.F₄ K)] (a : Fin 4) :
    (fixedOrbitNegative K (RingEquiv.refl K) a).map (signedFixedToOriginal K true)=
      (originalSimpleHom K true a).range := by
  rw [fixedOrbitNegative_native_range,MonoidHom.map_range]
  rfl

end SymmetricSubgroupAsymptotics.CFSGFFourE6OriginalSimpleRootRanges
