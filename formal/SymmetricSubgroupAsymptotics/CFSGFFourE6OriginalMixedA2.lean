import SymmetricSubgroupAsymptotics.CFSGFFourE6OriginalA2
import SymmetricSubgroupAsymptotics.CFSGE6GeckPairedMixedA2

/-! Literal opposite-simple coefficient-one A2 incidence on both native
F4 end edges, proved through the SAME actual J projection. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Classical commutatorElement
namespace SymmetricSubgroupAsymptotics.CFSGFFourE6OriginalMixedA2
open CFSGFFourE6OriginalA2 CFSGFFourE6SimpleGeneratedParameters
open CFSGFFourE6OriginalSimpleParameters CFSGFFourE6GeneratedOriginalProjection
open CFSGE6GeckPairedMixedA2 CFSGE6GeckSignedSimpleParameters
open CFSGE6GeckFixedOrbitRootGroups CFSGTwistedE6GeckPairedA2Commutator
open CFSGTwistedE6GeckDiagramCovariance CFSGTwistedE6RelativeWeylOrbits
open CFSGTwistedE6GeckRelativeRootGenerated CFSGTwistedE6FixedA2
open CFSGE6GeckRelativeSimpleHom CFSGNormTwoGeckMixedAdjacentCollecting
open CFSGExceptionalNormTwoBases CFSGExceptionalCartanPositiveDefinite
open CFSGSerreQuadraticMatrix CFSGSerreQuadraticWeylWord CFSG.Models.Chevalley

private theorem paired_val (K : Type) [Field K] (neg : Bool) (i : Fin 2) (a : K) :
    (simpleInGenerated K neg (pairedOrbit i) (Multiplicative.ofAdd a)).val=
      rawPairedHom K (RingEquiv.refl K) neg i (Multiplicative.ofAdd a) := by
  rw [simpleInGenerated_val]
  fin_cases i <;> rfl

private theorem singleton_val (K : Type) [Field K] (neg : Bool) (i : Fin 2) (a : K) :
    (simpleInGenerated K neg (singletonOrbit i) (Multiplicative.ofAdd a)).val=
      canonicalRoot rawData K neg (node i) a := by
  rw [simpleInGenerated_val]
  fin_cases i <;> rfl

theorem original_paired_mixed_commutator (K : Type) [Field K] [Finite K]
    [IsSimpleGroup (Projective CartanMatrix.F₄ K)] (i j : Fin 2) (hij : i≠j) (a b : K) :
    ⁅originalSimpleHom K true (pairedOrbit i) (Multiplicative.ofAdd a),
      sumOriginalHom K (pairedOrbit i) (pairedOrbit j) (Multiplicative.ofAdd b)⁆=
    originalSimpleHom K false (pairedOrbit j) (Multiplicative.ofAdd (a*b)) := by
  let W := simpleWeylInGenerated K (pairedOrbit i)
  have hw : W.val=pairedMatrixWeyl K i := by
    change (simpleWeylInGenerated K (pairedOrbit i)).val=_
    rw [simpleWeylInGenerated_val]
    fin_cases i <;> simp [pairedOrbit,orbitWord,canonicalWord,pairedMatrixWeyl] <;> rfl
  have hJ : ⁅simpleInGenerated K true (pairedOrbit i) (Multiplicative.ofAdd a),
      W*simpleInGenerated K false (pairedOrbit j) (Multiplicative.ofAdd b)*W⁻¹⁆=
    simpleInGenerated K false (pairedOrbit j) (Multiplicative.ofAdd (a*b)) := by
    apply Subtype.ext
    change ⁅(simpleInGenerated K true (pairedOrbit i) (Multiplicative.ofAdd a)).val,
      W.val*(simpleInGenerated K false (pairedOrbit j) (Multiplicative.ofAdd b)).val*W.val⁻¹⁆=
        (simpleInGenerated K false (pairedOrbit j) (Multiplicative.ofAdd (a*b))).val
    simp only [paired_val,hw]
    exact paired_mixed_adjacent K (RingEquiv.refl K) i j hij a b
  simpa only [map_commutatorElement,map_mul,map_inv,simpleInGenerated_original] using
    congrArg (generatedToOriginal K) hJ

theorem original_singleton_mixed_commutator (K : Type) [Field K] [Finite K]
    [IsSimpleGroup (Projective CartanMatrix.F₄ K)] (i j : Fin 2) (hij : i≠j) (a b : K) :
    ⁅originalSimpleHom K true (singletonOrbit i) (Multiplicative.ofAdd a),
      sumOriginalHom K (singletonOrbit i) (singletonOrbit j) (Multiplicative.ofAdd b)⁆=
    originalSimpleHom K false (singletonOrbit j) (Multiplicative.ofAdd (a*b)) := by
  let W := simpleWeylInGenerated K (singletonOrbit i)
  have hw : W.val=canonicalWeyl rawData K (node i) := by
    change (simpleWeylInGenerated K (singletonOrbit i)).val=_
    rw [simpleWeylInGenerated_val]
    fin_cases i <;> simp [singletonOrbit,orbitWord,canonicalWord,node] <;> rfl
  have hc : CFSGGeckSerreRepresentation.cartan E6Base E6Index (node i) (node j)= -1 := by
    rw [E6_cartan]
    fin_cases i <;> fin_cases j <;> first | exact (hij rfl).elim | decide
  have hc' : CFSGGeckSerreRepresentation.cartan E6Base E6Index (node j) (node i)= -1 := by
    rw [E6_cartan]
    fin_cases i <;> fin_cases j <;> first | exact (hij rfl).elim | decide
  have hJ : ⁅simpleInGenerated K true (singletonOrbit i) (Multiplicative.ofAdd a),
      W*simpleInGenerated K false (singletonOrbit j) (Multiplicative.ofAdd b)*W⁻¹⁆=
    simpleInGenerated K false (singletonOrbit j) (Multiplicative.ofAdd (a*b)) := by
    apply Subtype.ext
    change ⁅(simpleInGenerated K true (singletonOrbit i) (Multiplicative.ofAdd a)).val,
      W.val*(simpleInGenerated K false (singletonOrbit j) (Multiplicative.ofAdd b)).val*W.val⁻¹⁆=
        (simpleInGenerated K false (singletonOrbit j) (Multiplicative.ofAdd (a*b))).val
    simp only [singleton_val,hw]
    exact mixed_adjacent_word CartanMatrix.E₆ CartanMatrix.E₆_transpose E6_positive_definite
      E6Base E6Index K (node i) (node j) hc hc' a b
  simpa only [map_commutatorElement,map_mul,map_inv,simpleInGenerated_original] using
    congrArg (generatedToOriginal K) hJ

end SymmetricSubgroupAsymptotics.CFSGFFourE6OriginalMixedA2
