import SymmetricSubgroupAsymptotics.CFSGFFourE6GeneratedOriginalProjection
import SymmetricSubgroupAsymptotics.CFSGFFourE6OriginalSimpleParameters
import SymmetricSubgroupAsymptotics.CFSGE6GeckRelativeSimpleHom

/-! Native F4 signed simple parameters and their rank-one Weyl words
inside the SAME diagram-fixed E6 root-generated subgroup J. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics.CFSGFFourE6SimpleGeneratedParameters
open CFSGFFourE6GeneratedOriginalProjection CFSGFFourE6OriginalSimpleParameters
open CFSGTwistedE6GeckRelativeRootGenerated CFSGE6GeckRelativeSimpleHom
open CFSGTwistedE6GeckDiagramCovariance CFSGTwistedE6RelativeWeylOrbits
open CFSGSerreQuadraticWeylWord CFSG.Models.Chevalley

def simpleInGenerated (K : Type) [Field K] (neg : Bool) (i : Fin 4) :
    Multiplicative K→*fixedRootGenerated K (RingEquiv.refl K) :=
  (Subgroup.inclusion (signedFixed_le_generated K (RingEquiv.refl K) neg)).comp
    (foldedFixedHom K neg i)

theorem simpleInGenerated_val (K : Type) [Field K] (neg : Bool) (i : Fin 4) (a : Multiplicative K) :
    (simpleInGenerated K neg i a).val=rawOrbitHom K (RingEquiv.refl K) neg i a := by
  change (foldedFixedHom K neg i a).val=_
  rw [foldedFixedHom_val_as_raw]
  fin_cases i <;> rfl

theorem simpleInGenerated_original (K : Type) [Field K] [Finite K]
    [IsSimpleGroup (Projective CartanMatrix.F₄ K)] (neg : Bool) (i : Fin 4) (a : Multiplicative K) :
    generatedToOriginal K (simpleInGenerated K neg i a)=originalSimpleHom K neg i a := rfl

def simpleWeylInGenerated (K : Type) [Field K] (i : Fin 4) :
    fixedRootGenerated K (RingEquiv.refl K) :=
  simpleInGenerated K false i (Multiplicative.ofAdd 1)*
    (simpleInGenerated K true i (Multiplicative.ofAdd 1))⁻¹*
      simpleInGenerated K false i (Multiplicative.ofAdd 1)

theorem simpleWeylInGenerated_val (K : Type) [Field K] (i : Fin 4) :
    (simpleWeylInGenerated K i).val=canonicalWord rawData K (orbitWord i) := by
  change (simpleInGenerated K false i (Multiplicative.ofAdd 1)).val*
    (simpleInGenerated K true i (Multiplicative.ofAdd 1)).val⁻¹*
      (simpleInGenerated K false i (Multiplicative.ofAdd 1)).val=_
  simp only [simpleInGenerated_val]
  exact (rawOrbitHom_word K (RingEquiv.refl K) i).symm

end SymmetricSubgroupAsymptotics.CFSGFFourE6SimpleGeneratedParameters
