import SymmetricSubgroupAsymptotics.CFSGTwistedE6GeckOriginalPairedA2
import SymmetricSubgroupAsymptotics.CFSGNormTwoGeckParameterizedCollecting

/-! The singleton edge is an actual coefficient-one A2 over the fixed
coefficient subfield, inside the ORIGINAL twisted E6 group. Its two
parameters are independent, including in characteristics two and three. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics.CFSGTwistedE6GeckOriginalSingletonA2
open CFSGTwistedE6GeckOriginalPairedA2 CFSGTwistedE6GeckOriginalSimpleParameters
open CFSGTwistedE6GeckOriginalProjection CFSGTwistedE6GeckOriginalOppositeAlignment
open CFSGTwistedE6GeckDiagramCovariance CFSGTwistedE6GeckRelativeRootGenerated
open CFSGE6GeckFixedSimpleParameters CFSGE6GeckFixedOrbitRootGroups
open CFSGTwistedE6RelativeWeylOrbits CFSGTwistedE6FixedA2
open CFSGNormTwoGeckParameterizedCollecting CFSGSerreQuadraticMatrix CFSGSerreQuadraticWeylWord
open CFSGExceptionalNormTwoBases CFSGExceptionalCartanPositiveDefinite CFSGSerreOrdinaryTwists

abbrev Coefficient (q : CFSG.PrimePower) :=
  fixedCoefficient (q.Extension 2) (definingFieldAutomorphism q 2)

def singletonInGenerated (q : CFSG.PrimePower) (j : Fin 2) :
    Multiplicative (Coefficient q)→*fixedRootGenerated (q.Extension 2) (definingFieldAutomorphism q 2) :=
  (signedFixedToGenerated q false).comp
    (singletonFixedHom (q.Extension 2) (definingFieldAutomorphism q 2) false j)

def singletonSumOriginalHom (q : CFSG.PrimePower) [IsSimpleGroup (CFSG.Models.TwistedE6 q)]
    (i j : Fin 2) : Multiplicative (Coefficient q)→*CFSG.Models.TwistedE6 q :=
  (MulAut.conj (generatedToOriginal q (simpleWeylGenerated q (singletonOrbit i)))).toMonoidHom.comp
    (singletonOriginalHom q false j)

theorem singletonSumOriginalHom_injective (q : CFSG.PrimePower)
    [IsSimpleGroup (CFSG.Models.TwistedE6 q)] (i j : Fin 2) :
    Function.Injective (singletonSumOriginalHom q i j) :=
  (MulAut.conj _).injective.comp (singletonOriginalHom_injective q false j)

theorem original_singleton_adjacent_commutator (q : CFSG.PrimePower)
    [IsSimpleGroup (CFSG.Models.TwistedE6 q)] (i j : Fin 2) (hij : i≠j)
    (a b : Coefficient q) :
    singletonOriginalHom q false i (Multiplicative.ofAdd a)*
      singletonOriginalHom q false j (Multiplicative.ofAdd b)*
      (singletonOriginalHom q false i (Multiplicative.ofAdd a))⁻¹*
      (singletonOriginalHom q false j (Multiplicative.ofAdd b))⁻¹=
        singletonSumOriginalHom q i j (Multiplicative.ofAdd (a*b)) := by
  have hw : (simpleWeylGenerated q (singletonOrbit i)).val=
      canonicalWeyl rawData (q.Extension 2) (node i) := by
    rw [simpleWeylGenerated_val]
    fin_cases i <;> simp [singletonOrbit,orbitWord,canonicalWord,node] <;> rfl
  have hcartan : CFSGGeckSerreRepresentation.cartan E6Base E6Index (node i) (node j)= -1 := by
    rw [E6_cartan]
    fin_cases i <;> fin_cases j <;> first | exact (hij rfl).elim | decide
  have hraw := adjacent_word CartanMatrix.E₆ CartanMatrix.E₆_transpose
    E6_positive_definite E6Base E6Index (q.Extension 2) (node i) (node j) hcartan
      (a : q.Extension 2) (b : q.Extension 2)
  have hJ : singletonInGenerated q i (Multiplicative.ofAdd a)*singletonInGenerated q j (Multiplicative.ofAdd b)*
      (singletonInGenerated q i (Multiplicative.ofAdd a))⁻¹*(singletonInGenerated q j (Multiplicative.ofAdd b))⁻¹=
      simpleWeylGenerated q (singletonOrbit i)*singletonInGenerated q j (Multiplicative.ofAdd (a*b))*
        (simpleWeylGenerated q (singletonOrbit i))⁻¹ := by
    apply Subtype.ext
    change canonicalRoot rawData (q.Extension 2) false (node i) (a : q.Extension 2)*
      canonicalRoot rawData (q.Extension 2) false (node j) (b : q.Extension 2)*
      (canonicalRoot rawData (q.Extension 2) false (node i) (a : q.Extension 2))⁻¹*
      (canonicalRoot rawData (q.Extension 2) false (node j) (b : q.Extension 2))⁻¹=
      (simpleWeylGenerated q (singletonOrbit i)).val*
        canonicalRoot rawData (q.Extension 2) false (node j) ((a*b : Coefficient q) : q.Extension 2)*
        ((simpleWeylGenerated q (singletonOrbit i)).val)⁻¹
    rw [hw]
    simpa only [mul_comm (b : q.Extension 2) (a : q.Extension 2)] using hraw
  simpa only [map_mul,map_inv] using congrArg (generatedToOriginal q) hJ

end SymmetricSubgroupAsymptotics.CFSGTwistedE6GeckOriginalSingletonA2
