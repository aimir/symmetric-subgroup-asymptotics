import SymmetricSubgroupAsymptotics.CFSGTwistedE6GeckOriginalSingletonA2
import SymmetricSubgroupAsymptotics.CFSGE6GeckMiddlePairedCollecting

/-! The genuine middle-edge two-factor relation in the ORIGINAL model.
The singleton factor has its actual norm parameter, while the paired
factor has coefficient -ab. No factor uniqueness or field agreement is
assumed in this transport of the literal J word identity. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Classical commutatorElement
namespace SymmetricSubgroupAsymptotics.CFSGTwistedE6GeckOriginalMiddleCollecting
open CFSGTwistedE6GeckOriginalPairedA2 CFSGTwistedE6GeckOriginalSingletonA2
open CFSGTwistedE6GeckOriginalSimpleParameters CFSGTwistedE6GeckOriginalProjection
open CFSGTwistedE6GeckDiagramCovariance CFSGE6GeckFixedSimpleParameters
open CFSGE6GeckSignedSimpleParameters CFSGE6GeckMiddlePairedCollecting
open CFSGE6GeckMiddleAThreeCollecting CFSGTwistedE6RelativeWeylOrbits
open CFSGSerreQuadraticMatrix CFSGSerreQuadraticWeylWord CFSGSerreOrdinaryTwists

def normCoefficient (q : CFSG.PrimePower) (a : q.Extension 2) : Coefficient q :=
  ⟨a*definingFieldAutomorphism q 2 a,by
    change definingFieldAutomorphism q 2 (a*definingFieldAutomorphism q 2 a)=a*definingFieldAutomorphism q 2 a
    rw [map_mul,coefficient_involutive q a]
    exact mul_comm _ _⟩

def middleLongOriginalHom (q : CFSG.PrimePower) [IsSimpleGroup (CFSG.Models.TwistedE6 q)] :
    Multiplicative (Coefficient q)→*CFSG.Models.TwistedE6 q :=
  (MulAut.conj (generatedToOriginal q (simpleWeylGenerated q 1))).toMonoidHom.comp
    (singletonOriginalHom q false 1)

def middleShortOriginalHom (q : CFSG.PrimePower) [IsSimpleGroup (CFSG.Models.TwistedE6 q)] :
    Multiplicative (q.Extension 2)→*CFSG.Models.TwistedE6 q :=
  (MulAut.conj (generatedToOriginal q (simpleWeylGenerated q 2))).toMonoidHom.comp
    (pairedOriginalHom q false 1)

theorem middleLongOriginalHom_injective (q : CFSG.PrimePower)
    [IsSimpleGroup (CFSG.Models.TwistedE6 q)] : Function.Injective (middleLongOriginalHom q) :=
  (MulAut.conj _).injective.comp (singletonOriginalHom_injective q false 1)

theorem middleShortOriginalHom_injective (q : CFSG.PrimePower)
    [IsSimpleGroup (CFSG.Models.TwistedE6 q)] : Function.Injective (middleShortOriginalHom q) :=
  (MulAut.conj _).injective.comp (pairedOriginalHom_injective q false 1)

theorem original_middle_commutator (q : CFSG.PrimePower)
    [IsSimpleGroup (CFSG.Models.TwistedE6 q)] (a : q.Extension 2) (b : Coefficient q) :
    ⁅pairedOriginalHom q false 1 (Multiplicative.ofAdd a),
      singletonOriginalHom q false 1 (Multiplicative.ofAdd b)⁆=
      middleLongOriginalHom q (Multiplicative.ofAdd (normCoefficient q a*b))*
        middleShortOriginalHom q (Multiplicative.ofAdd (-(a*(b : q.Extension 2)))) := by
  have hw1 : (simpleWeylGenerated q 1).val=
      canonicalWeyl rawData (q.Extension 2) 2*canonicalWeyl rawData (q.Extension 2) 4 := by
    rw [simpleWeylGenerated_val]
    simp [orbitWord,canonicalWord]
  have hw2 : (simpleWeylGenerated q 2).val=canonicalWeyl rawData (q.Extension 2) 3 := by
    rw [simpleWeylGenerated_val]
    simp [orbitWord,canonicalWord]
  have hJ : ⁅pairedInGenerated q 1 (Multiplicative.ofAdd a),singletonInGenerated q 1 (Multiplicative.ofAdd b)⁆=
      (simpleWeylGenerated q 1*singletonInGenerated q 1 (Multiplicative.ofAdd (normCoefficient q a*b))*
        (simpleWeylGenerated q 1)⁻¹)*
      (simpleWeylGenerated q 2*pairedInGenerated q 1 (Multiplicative.ofAdd (-(a*(b : q.Extension 2))))*
        (simpleWeylGenerated q 2)⁻¹) := by
    apply Subtype.ext
    change ⁅rawPairedHom (q.Extension 2) (definingFieldAutomorphism q 2) false 1 (Multiplicative.ofAdd a),
      rawSingletonHom (q.Extension 2) false 1 (Multiplicative.ofAdd (b : q.Extension 2))⁆=
      ((simpleWeylGenerated q 1).val*canonicalRoot rawData (q.Extension 2) false 3
        (a*definingFieldAutomorphism q 2 a*(b : q.Extension 2))*(simpleWeylGenerated q 1).val⁻¹)*
      ((simpleWeylGenerated q 2).val*rawPairedHom (q.Extension 2) (definingFieldAutomorphism q 2) false 1
        (Multiplicative.ofAdd (-(a*(b : q.Extension 2))))*(simpleWeylGenerated q 2).val⁻¹)
    rw [hw1,hw2]
    exact middle_paired_commutator (q.Extension 2) (definingFieldAutomorphism q 2) a b b.property
  simpa only [map_commutatorElement,map_mul,map_inv] using congrArg (generatedToOriginal q) hJ

end SymmetricSubgroupAsymptotics.CFSGTwistedE6GeckOriginalMiddleCollecting
