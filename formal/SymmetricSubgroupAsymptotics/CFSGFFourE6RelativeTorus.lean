import SymmetricSubgroupAsymptotics.CFSGFFourE6SimpleGeneratedParameters
import SymmetricSubgroupAsymptotics.CFSGE6GeckPairedParameterizedWeyl
import SymmetricSubgroupAsymptotics.CFSGSemilinearRankOneWord

/-! Native F4 rank-one torus words inside the actual J source and their
original semilinear Weyl images. The raw singleton/paired values are the
already checked E6 rank-one torus matrices at sigma=id. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics.CFSGFFourE6RelativeTorus
open CFSGFFourE6SimpleGeneratedParameters CFSGFFourE6OriginalSimpleParameters
open CFSGFFourE6GeneratedOriginalProjection CFSGTwistedE6GeckRelativeRootGenerated
open CFSGE6GeckSignedSimpleParameters CFSGE6GeckRelativeSimpleHom
open CFSGE6GeckFixedOrbitRootGroups CFSGE6GeckPairedParameterizedWeyl
open CFSGTwistedE6GeckDiagramCovariance CFSGTwistedE6GeckPairedA2Commutator
open CFSGTwistedE6RelativeWeylOrbits CFSGTwistedE6FixedA2
open CFSGNormTwoGeckParameterizedTorus CFSGNormTwoGeckParameterizedWeyl
open CFSGExceptionalNormTwoBases CFSGExceptionalCartanPositiveDefinite
open CFSGSerreQuadraticMatrix CFSGSerreQuadraticWeylWord
open CFSGSemilinearRankOneWord CFSG.Models.Chevalley

def scaledWeylInGenerated (K : Type) [Field K] (i : Fin 4) (t : Kˣ) :
    fixedRootGenerated K (RingEquiv.refl K) :=
  simpleInGenerated K false i (Multiplicative.ofAdd (t : K))*
    simpleInGenerated K true i (Multiplicative.ofAdd (-(t : K)⁻¹))*
      simpleInGenerated K false i (Multiplicative.ofAdd (t : K))

def torusInGenerated (K : Type) [Field K] (i : Fin 4) (t : Kˣ) :
    fixedRootGenerated K (RingEquiv.refl K) :=
  scaledWeylInGenerated K i t*(simpleWeylInGenerated K i)⁻¹

private theorem paired_parameter_val (K : Type) [Field K] (neg : Bool) (i : Fin 2) (a : K) :
    (simpleInGenerated K neg (pairedOrbit i) (Multiplicative.ofAdd a)).val=
      rawPairedHom K (RingEquiv.refl K) neg i (Multiplicative.ofAdd a) := by
  rw [simpleInGenerated_val]
  fin_cases i <;> rfl

private theorem singleton_parameter_val (K : Type) [Field K] (neg : Bool) (i : Fin 2) (a : K) :
    (simpleInGenerated K neg (singletonOrbit i) (Multiplicative.ofAdd a)).val=
      canonicalRoot rawData K neg (node i) a := by
  rw [simpleInGenerated_val]
  fin_cases i <;> rfl

theorem torusInGenerated_paired_val (K : Type) [Field K] (i : Fin 2) (t : Kˣ) :
    (torusInGenerated K (pairedOrbit i) t).val=pairedParameterTorus K (RingEquiv.refl K) i t := by
  have hw : (simpleWeylInGenerated K (pairedOrbit i)).val=pairedMatrixWeyl K i := by
    rw [simpleWeylInGenerated_val]
    fin_cases i <;> simp [pairedOrbit,orbitWord,canonicalWord,pairedMatrixWeyl] <;> rfl
  change ((simpleInGenerated K false (pairedOrbit i) (Multiplicative.ofAdd (t : K))).val*
      (simpleInGenerated K true (pairedOrbit i) (Multiplicative.ofAdd (-(t : K)⁻¹))).val*
      (simpleInGenerated K false (pairedOrbit i) (Multiplicative.ofAdd (t : K))).val)*
        (simpleWeylInGenerated K (pairedOrbit i)).val⁻¹=_
  simp only [paired_parameter_val,hw]
  rfl

theorem torusInGenerated_singleton_val (K : Type) [Field K] (i : Fin 2) (t : Kˣ) :
    (torusInGenerated K (singletonOrbit i) t).val=
      parameterTorus CartanMatrix.E₆ CartanMatrix.E₆_transpose E6_positive_definite
        E6Base E6Index K (node i) t := by
  have hw : (simpleWeylInGenerated K (singletonOrbit i)).val=canonicalWeyl rawData K (node i) := by
    rw [simpleWeylInGenerated_val]
    fin_cases i <;> simp [singletonOrbit,orbitWord,canonicalWord,node] <;> rfl
  change ((simpleInGenerated K false (singletonOrbit i) (Multiplicative.ofAdd (t : K))).val*
      (simpleInGenerated K true (singletonOrbit i) (Multiplicative.ofAdd (-(t : K)⁻¹))).val*
      (simpleInGenerated K false (singletonOrbit i) (Multiplicative.ofAdd (t : K))).val)*
        (simpleWeylInGenerated K (singletonOrbit i)).val⁻¹=_
  simp only [singleton_parameter_val,hw]
  rw [parameterTorus,CFSGNormTwoGeckWeylSquareTorus.parameterWeyl_one]
  rfl

theorem original_weyl_image (K : Type) [Field K] [Finite K]
    [IsSimpleGroup (Projective CartanMatrix.F₄ K)] (f : MulAut (Projective CartanMatrix.F₄ K))
    (i : Fin 4) (tau : RingAut K) (t : Kˣ)
    (hpos : ∀a,f (originalSimpleHom K false i (Multiplicative.ofAdd a))=
      originalSimpleHom K false i (Multiplicative.ofAdd ((t : K)*tau a)))
    (hneg : ∀a,f (originalSimpleHom K true i (Multiplicative.ofAdd a))=
      originalSimpleHom K true i (Multiplicative.ofAdd ((t : K)⁻¹*tau a))) :
    f (generatedToOriginal K (simpleWeylInGenerated K i))=
      generatedToOriginal K (torusInGenerated K i t)*generatedToOriginal K (simpleWeylInGenerated K i) := by
  let u := originalSimpleHom K false i
  let v := originalSimpleHom K true i
  have hW : generatedToOriginal K (simpleWeylInGenerated K i)=
      u (Multiplicative.ofAdd 1)*(v (Multiplicative.ofAdd 1))⁻¹*u (Multiplicative.ofAdd 1) := by
    simp only [simpleWeylInGenerated,map_mul,map_inv,simpleInGenerated_original]
    rfl
  have hS : generatedToOriginal K (scaledWeylInGenerated K i t)=
      u (Multiplicative.ofAdd (t : K))*v (Multiplicative.ofAdd (-(t : K)⁻¹))*u (Multiplicative.ofAdd (t : K)) := by
    simp only [scaledWeylInGenerated,map_mul,simpleInGenerated_original]
    rfl
  apply image_eq_torus_mul (generatedToOriginal K) f.toMonoidHom
    (scaledWeylInGenerated K i t) (simpleWeylInGenerated K i)
  exact (congrArg f hW).trans ((image_rank_one_word u v f.toMonoidHom tau t hpos hneg).trans hS.symm)

end SymmetricSubgroupAsymptotics.CFSGFFourE6RelativeTorus
