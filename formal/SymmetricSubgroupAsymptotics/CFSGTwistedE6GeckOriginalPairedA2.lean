import SymmetricSubgroupAsymptotics.CFSGTwistedE6GeckOriginalRankOneWitness
import SymmetricSubgroupAsymptotics.CFSGTwistedE6GeckPairedA2Commutator
import SymmetricSubgroupAsymptotics.CFSGCommutatorParameterRange

/-! The paired A2 commutator and its third root chart in the ORIGINAL
twisted E6 model. All parameters range independently over the actual
quadratic extension; the coefficient-one identity is proved by the same
literal matrix words and then pushed through the original projection. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics.CFSGTwistedE6GeckOriginalPairedA2
open CFSGTwistedE6GeckOriginalRankOneWitness CFSGTwistedE6GeckOriginalSimpleParameters
open CFSGTwistedE6GeckOriginalProjection CFSGTwistedE6GeckOriginalOppositeAlignment
open CFSGTwistedE6GeckRelativeRootGenerated CFSGTwistedE6GeckDiagramCovariance
open CFSGE6GeckRelativeSimpleHom CFSGE6GeckFixedOrbitRootGroups CFSGE6GeckFixedSimpleParameters
open CFSGTwistedE6GeckPairedA2Commutator CFSGTwistedE6RelativeWeylOrbits
open CFSGSerreOrdinaryTwists CFSGSerreQuadraticWeylWord

def simpleWeylGenerated (q : CFSG.PrimePower) (a : Fin 4) :
    fixedRootGenerated (q.Extension 2) (definingFieldAutomorphism q 2) :=
  orbitOneInGenerated q false a*(orbitOneInGenerated q true a)⁻¹*orbitOneInGenerated q false a

theorem simpleWeylGenerated_val (q : CFSG.PrimePower) (a : Fin 4) :
    (simpleWeylGenerated q a).val=canonicalWord rawData (q.Extension 2) (orbitWord a) :=
  (rawOrbitHom_word (q.Extension 2) (definingFieldAutomorphism q 2) a).symm

def pairedInGenerated (q : CFSG.PrimePower) (j : Fin 2) :
    Multiplicative (q.Extension 2)→*fixedRootGenerated (q.Extension 2) (definingFieldAutomorphism q 2) :=
  (signedFixedToGenerated q false).comp
    (pairedFixedHom (q.Extension 2) (definingFieldAutomorphism q 2) (coefficient_involutive q) false j)

def pairedSumOriginalHom (q : CFSG.PrimePower) [IsSimpleGroup (CFSG.Models.TwistedE6 q)]
    (i j : Fin 2) : Multiplicative (q.Extension 2)→*CFSG.Models.TwistedE6 q :=
  (MulAut.conj (generatedToOriginal q (simpleWeylGenerated q (pairedOrbit i)))).toMonoidHom.comp
    (pairedOriginalHom q false j)

theorem pairedSumOriginalHom_injective (q : CFSG.PrimePower)
    [IsSimpleGroup (CFSG.Models.TwistedE6 q)] (i j : Fin 2) :
    Function.Injective (pairedSumOriginalHom q i j) :=
  (MulAut.conj _).injective.comp (pairedOriginalHom_injective q false j)

theorem original_paired_adjacent_commutator (q : CFSG.PrimePower)
    [IsSimpleGroup (CFSG.Models.TwistedE6 q)] (i j : Fin 2) (hij : i≠j)
    (a b : q.Extension 2) :
    pairedOriginalHom q false i (Multiplicative.ofAdd a)*
      pairedOriginalHom q false j (Multiplicative.ofAdd b)*
      (pairedOriginalHom q false i (Multiplicative.ofAdd a))⁻¹*
      (pairedOriginalHom q false j (Multiplicative.ofAdd b))⁻¹=
        pairedSumOriginalHom q i j (Multiplicative.ofAdd (a*b)) := by
  have hw : (simpleWeylGenerated q (pairedOrbit i)).val=pairedMatrixWeyl (q.Extension 2) i := by
    rw [simpleWeylGenerated_val]
    fin_cases i <;> simp [pairedOrbit,orbitWord,canonicalWord,pairedMatrixWeyl] <;> rfl
  have hraw := paired_adjacent_commutator (q.Extension 2) (definingFieldAutomorphism q 2) i j hij a b
  have hJ : pairedInGenerated q i (Multiplicative.ofAdd a)*pairedInGenerated q j (Multiplicative.ofAdd b)*
      (pairedInGenerated q i (Multiplicative.ofAdd a))⁻¹*(pairedInGenerated q j (Multiplicative.ofAdd b))⁻¹=
      simpleWeylGenerated q (pairedOrbit i)*pairedInGenerated q j (Multiplicative.ofAdd (a*b))*
        (simpleWeylGenerated q (pairedOrbit i))⁻¹ := by
    apply Subtype.ext
    change pairedMatrixRoot (q.Extension 2) (definingFieldAutomorphism q 2) i a*
      pairedMatrixRoot (q.Extension 2) (definingFieldAutomorphism q 2) j b*
      (pairedMatrixRoot (q.Extension 2) (definingFieldAutomorphism q 2) i a)⁻¹*
      (pairedMatrixRoot (q.Extension 2) (definingFieldAutomorphism q 2) j b)⁻¹=
      (simpleWeylGenerated q (pairedOrbit i)).val*
        pairedMatrixRoot (q.Extension 2) (definingFieldAutomorphism q 2) j (a*b)*
        ((simpleWeylGenerated q (pairedOrbit i)).val)⁻¹
    rw [hw]
    simpa only [mul_comm b a] using hraw
  simpa only [map_mul,map_inv] using congrArg (generatedToOriginal q) hJ

end SymmetricSubgroupAsymptotics.CFSGTwistedE6GeckOriginalPairedA2
