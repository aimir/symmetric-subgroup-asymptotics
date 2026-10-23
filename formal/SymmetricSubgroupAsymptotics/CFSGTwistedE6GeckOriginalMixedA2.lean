import SymmetricSubgroupAsymptotics.CFSGTwistedE6GeckOriginalSingletonA2
import SymmetricSubgroupAsymptotics.CFSGE6GeckPairedMixedA2

/-! Literal opposite-simple A2 identities in the ORIGINAL twisted E6
model. Both the extension-parameter paired edge and fixed-subfield
singleton edge retain coefficient one and independent parameters. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Classical commutatorElement
namespace SymmetricSubgroupAsymptotics.CFSGTwistedE6GeckOriginalMixedA2
open CFSGTwistedE6GeckOriginalPairedA2 CFSGTwistedE6GeckOriginalSingletonA2
open CFSGTwistedE6GeckOriginalSimpleParameters CFSGTwistedE6GeckOriginalOppositeAlignment
open CFSGTwistedE6GeckOriginalProjection CFSGTwistedE6GeckDiagramCovariance
open CFSGE6GeckFixedSimpleParameters CFSGE6GeckFixedOrbitRootGroups
open CFSGE6GeckSignedSimpleParameters CFSGE6GeckPairedMixedA2
open CFSGTwistedE6GeckPairedA2Commutator CFSGTwistedE6RelativeWeylOrbits
open CFSGSerreQuadraticWeylWord CFSGSerreQuadraticMatrix CFSGSerreOrdinaryTwists
open CFSGTwistedE6FixedA2 CFSGExceptionalNormTwoBases CFSGExceptionalCartanPositiveDefinite
open CFSGNormTwoGeckMixedAdjacentCollecting

theorem original_paired_mixed_commutator (q : CFSG.PrimePower)
    [IsSimpleGroup (CFSG.Models.TwistedE6 q)] (i j : Fin 2) (hij : i≠j)
    (a b : q.Extension 2) :
    ⁅pairedOriginalHom q true i (Multiplicative.ofAdd a),
      pairedSumOriginalHom q i j (Multiplicative.ofAdd b)⁆=
      pairedOriginalHom q false j (Multiplicative.ofAdd (a*b)) := by
  let n := (signedFixedToGenerated q true).comp
    (pairedFixedHom (q.Extension 2) (definingFieldAutomorphism q 2) (coefficient_involutive q) true i)
  let W := simpleWeylGenerated q (pairedOrbit i)
  have hw : W.val=pairedMatrixWeyl (q.Extension 2) i := by
    change (simpleWeylGenerated q (pairedOrbit i)).val=pairedMatrixWeyl (q.Extension 2) i
    rw [simpleWeylGenerated_val]
    fin_cases i <;> simp [pairedOrbit,orbitWord,canonicalWord,pairedMatrixWeyl] <;> rfl
  have hJ : ⁅n (Multiplicative.ofAdd a),W*pairedInGenerated q j (Multiplicative.ofAdd b)*W⁻¹⁆=
      pairedInGenerated q j (Multiplicative.ofAdd (a*b)) := by
    apply Subtype.ext
    change ⁅rawPairedHom (q.Extension 2) (definingFieldAutomorphism q 2) true i (Multiplicative.ofAdd a),
      W.val*rawPairedHom (q.Extension 2) (definingFieldAutomorphism q 2) false j (Multiplicative.ofAdd b)*W.val⁻¹⁆=
      rawPairedHom (q.Extension 2) (definingFieldAutomorphism q 2) false j (Multiplicative.ofAdd (a*b))
    rw [hw]
    exact paired_mixed_adjacent (q.Extension 2) (definingFieldAutomorphism q 2) i j hij a b
  simpa only [map_commutatorElement,map_mul,map_inv] using congrArg (generatedToOriginal q) hJ

theorem original_singleton_mixed_commutator (q : CFSG.PrimePower)
    [IsSimpleGroup (CFSG.Models.TwistedE6 q)] (i j : Fin 2) (hij : i≠j)
    (a b : Coefficient q) :
    ⁅singletonOriginalHom q true i (Multiplicative.ofAdd a),
      singletonSumOriginalHom q i j (Multiplicative.ofAdd b)⁆=
      singletonOriginalHom q false j (Multiplicative.ofAdd (a*b)) := by
  let n := (signedFixedToGenerated q true).comp
    (singletonFixedHom (q.Extension 2) (definingFieldAutomorphism q 2) true i)
  let W := simpleWeylGenerated q (singletonOrbit i)
  have hw : W.val=canonicalWeyl rawData (q.Extension 2) (node i) := by
    change (simpleWeylGenerated q (singletonOrbit i)).val=canonicalWeyl rawData (q.Extension 2) (node i)
    rw [simpleWeylGenerated_val]
    fin_cases i <;> simp [singletonOrbit,orbitWord,canonicalWord,node] <;> rfl
  have hcartan : CFSGGeckSerreRepresentation.cartan E6Base E6Index (node i) (node j)= -1 := by
    rw [E6_cartan]
    fin_cases i <;> fin_cases j <;> first | exact (hij rfl).elim | decide
  have hcartan' : CFSGGeckSerreRepresentation.cartan E6Base E6Index (node j) (node i)= -1 := by
    rw [E6_cartan]
    fin_cases i <;> fin_cases j <;> first | exact (hij rfl).elim | decide
  have hJ : ⁅n (Multiplicative.ofAdd a),W*singletonInGenerated q j (Multiplicative.ofAdd b)*W⁻¹⁆=
      singletonInGenerated q j (Multiplicative.ofAdd (a*b)) := by
    apply Subtype.ext
    change ⁅canonicalRoot rawData (q.Extension 2) true (node i) (a : q.Extension 2),
      W.val*canonicalRoot rawData (q.Extension 2) false (node j) (b : q.Extension 2)*W.val⁻¹⁆=
      canonicalRoot rawData (q.Extension 2) false (node j) ((a*b : Coefficient q) : q.Extension 2)
    rw [hw]
    exact mixed_adjacent_word CartanMatrix.E₆ CartanMatrix.E₆_transpose E6_positive_definite
      E6Base E6Index (q.Extension 2) (node i) (node j) hcartan hcartan' a b
  simpa only [map_commutatorElement,map_mul,map_inv] using congrArg (generatedToOriginal q) hJ

end SymmetricSubgroupAsymptotics.CFSGTwistedE6GeckOriginalMixedA2
