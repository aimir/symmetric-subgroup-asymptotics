import SymmetricSubgroupAsymptotics.CFSGFFourE6SimpleGeneratedParameters
import SymmetricSubgroupAsymptotics.CFSGTwistedE6GeckPairedA2Commutator
import SymmetricSubgroupAsymptotics.CFSGNormTwoGeckParameterizedCollecting

/-! Both end edges of ORIGINAL F4 are literal coefficient-one A2
commutators on the native simple parameter charts. All parameters range
over K independently, including in characteristics two and three. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics.CFSGFFourE6OriginalA2
open CFSGFFourE6SimpleGeneratedParameters CFSGFFourE6OriginalSimpleParameters
open CFSGFFourE6GeneratedOriginalProjection CFSGTwistedE6GeckRelativeRootGenerated
open CFSGTwistedE6GeckDiagramCovariance CFSGTwistedE6GeckPairedA2Commutator
open CFSGE6GeckFixedOrbitRootGroups CFSGE6GeckRelativeSimpleHom
open CFSGTwistedE6FixedA2 CFSGTwistedE6PairedFixedRoots
open CFSGNormTwoGeckParameterizedCollecting CFSGSerreQuadraticMatrix
open CFSGSerreQuadraticWeylWord CFSGExceptionalNormTwoBases
open CFSGExceptionalCartanPositiveDefinite CFSG.Models.Chevalley
open CFSGTwistedE6RelativeWeylOrbits

def sumOriginalHom (K : Type) [Field K] [Finite K]
    [IsSimpleGroup (Projective CartanMatrix.F₄ K)] (i j : Fin 4) :
    Multiplicative K→*Projective CartanMatrix.F₄ K :=
  (MulAut.conj (generatedToOriginal K (simpleWeylInGenerated K i))).toMonoidHom.comp
    (originalSimpleHom K false j)

theorem sumOriginalHom_injective (K : Type) [Field K] [Finite K]
    (p : ℕ) [Fact p.Prime] [CharP K p] [IsSimpleGroup (Projective CartanMatrix.F₄ K)]
    (i j : Fin 4) : Function.Injective (sumOriginalHom K i j) :=
  (MulAut.conj _).injective.comp (originalSimpleHom_injective K p false j)

private theorem simple_paired_val (K : Type) [Field K] (i : Fin 2) (a : K) :
    (simpleInGenerated K false (pairedOrbit i) (Multiplicative.ofAdd a)).val=
      pairedMatrixRoot K (RingEquiv.refl K) i a := by
  rw [simpleInGenerated_val]
  fin_cases i <;> rfl

private theorem simple_singleton_val (K : Type) [Field K] (i : Fin 2) (a : K) :
    (simpleInGenerated K false (singletonOrbit i) (Multiplicative.ofAdd a)).val=
      canonicalRoot rawData K false (node i) a := by
  rw [simpleInGenerated_val]
  fin_cases i <;> rfl

theorem generated_paired_commutator (K : Type) [Field K] (i j : Fin 2) (hij : i≠j) (a b : K) :
    simpleInGenerated K false (pairedOrbit i) (Multiplicative.ofAdd a)*
      simpleInGenerated K false (pairedOrbit j) (Multiplicative.ofAdd b)*
      (simpleInGenerated K false (pairedOrbit i) (Multiplicative.ofAdd a))⁻¹*
      (simpleInGenerated K false (pairedOrbit j) (Multiplicative.ofAdd b))⁻¹=
    simpleWeylInGenerated K (pairedOrbit i)*
      simpleInGenerated K false (pairedOrbit j) (Multiplicative.ofAdd (a*b))*
      (simpleWeylInGenerated K (pairedOrbit i))⁻¹ := by
  have hw : (simpleWeylInGenerated K (pairedOrbit i)).val=pairedMatrixWeyl K i := by
    rw [simpleWeylInGenerated_val]
    fin_cases i <;> simp [pairedOrbit,orbitWord,canonicalWord,pairedMatrixWeyl] <;> rfl
  apply Subtype.ext
  simp only [Subgroup.coe_mul,Subgroup.coe_inv,simple_paired_val]
  change pairedMatrixRoot K (RingEquiv.refl K) i a*pairedMatrixRoot K (RingEquiv.refl K) j b*
    (pairedMatrixRoot K (RingEquiv.refl K) i a)⁻¹*(pairedMatrixRoot K (RingEquiv.refl K) j b)⁻¹=
    (simpleWeylInGenerated K (pairedOrbit i)).val*
      pairedMatrixRoot K (RingEquiv.refl K) j (a*b)*
        ((simpleWeylInGenerated K (pairedOrbit i)).val)⁻¹
  rw [hw]
  simpa only [mul_comm b a] using paired_adjacent_commutator K (RingEquiv.refl K) i j hij a b

theorem generated_singleton_commutator (K : Type) [Field K] (i j : Fin 2) (hij : i≠j) (a b : K) :
    simpleInGenerated K false (singletonOrbit i) (Multiplicative.ofAdd a)*
      simpleInGenerated K false (singletonOrbit j) (Multiplicative.ofAdd b)*
      (simpleInGenerated K false (singletonOrbit i) (Multiplicative.ofAdd a))⁻¹*
      (simpleInGenerated K false (singletonOrbit j) (Multiplicative.ofAdd b))⁻¹=
    simpleWeylInGenerated K (singletonOrbit i)*
      simpleInGenerated K false (singletonOrbit j) (Multiplicative.ofAdd (a*b))*
      (simpleWeylInGenerated K (singletonOrbit i))⁻¹ := by
  have hw : (simpleWeylInGenerated K (singletonOrbit i)).val=canonicalWeyl rawData K (node i) := by
    rw [simpleWeylInGenerated_val]
    fin_cases i <;> simp [singletonOrbit,orbitWord,canonicalWord,node] <;> rfl
  have hcartan : CFSGGeckSerreRepresentation.cartan E6Base E6Index (node i) (node j)= -1 := by
    rw [E6_cartan]
    fin_cases i <;> fin_cases j <;> first | exact (hij rfl).elim | decide
  apply Subtype.ext
  simp only [Subgroup.coe_mul,Subgroup.coe_inv,simple_singleton_val]
  change canonicalRoot rawData K false (node i) a*canonicalRoot rawData K false (node j) b*
    (canonicalRoot rawData K false (node i) a)⁻¹*(canonicalRoot rawData K false (node j) b)⁻¹=
    (simpleWeylInGenerated K (singletonOrbit i)).val*canonicalRoot rawData K false (node j) (a*b)*
      ((simpleWeylInGenerated K (singletonOrbit i)).val)⁻¹
  rw [hw]
  simpa only [mul_comm b a] using adjacent_word CartanMatrix.E₆ CartanMatrix.E₆_transpose
    E6_positive_definite E6Base E6Index K (node i) (node j) hcartan a b

theorem original_paired_commutator (K : Type) [Field K] [Finite K]
    [IsSimpleGroup (Projective CartanMatrix.F₄ K)] (i j : Fin 2) (hij : i≠j) (a b : K) :
    originalSimpleHom K false (pairedOrbit i) (Multiplicative.ofAdd a)*
      originalSimpleHom K false (pairedOrbit j) (Multiplicative.ofAdd b)*
      (originalSimpleHom K false (pairedOrbit i) (Multiplicative.ofAdd a))⁻¹*
      (originalSimpleHom K false (pairedOrbit j) (Multiplicative.ofAdd b))⁻¹=
    sumOriginalHom K (pairedOrbit i) (pairedOrbit j) (Multiplicative.ofAdd (a*b)) := by
  simpa only [map_mul,map_inv,simpleInGenerated_original] using
    congrArg (generatedToOriginal K) (generated_paired_commutator K i j hij a b)

theorem original_singleton_commutator (K : Type) [Field K] [Finite K]
    [IsSimpleGroup (Projective CartanMatrix.F₄ K)] (i j : Fin 2) (hij : i≠j) (a b : K) :
    originalSimpleHom K false (singletonOrbit i) (Multiplicative.ofAdd a)*
      originalSimpleHom K false (singletonOrbit j) (Multiplicative.ofAdd b)*
      (originalSimpleHom K false (singletonOrbit i) (Multiplicative.ofAdd a))⁻¹*
      (originalSimpleHom K false (singletonOrbit j) (Multiplicative.ofAdd b))⁻¹=
    sumOriginalHom K (singletonOrbit i) (singletonOrbit j) (Multiplicative.ofAdd (a*b)) := by
  simpa only [map_mul,map_inv,simpleInGenerated_original] using
    congrArg (generatedToOriginal K) (generated_singleton_commutator K i j hij a b)

end SymmetricSubgroupAsymptotics.CFSGFFourE6OriginalA2
