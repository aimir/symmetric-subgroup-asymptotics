import SymmetricSubgroupAsymptotics.CFSGFFourE6SimpleGeneratedParameters
import SymmetricSubgroupAsymptotics.CFSGE6GeckMiddlePairedCollecting
import SymmetricSubgroupAsymptotics.CFSGE6GeckMiddleFactorInjective

/-! The original F4 middle commutator retains its literal a^2 b and
coefficient-one -ab factors. Their positive matrix witnesses and actual
positive projection injection recover the second original factor. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Classical commutatorElement
namespace SymmetricSubgroupAsymptotics.CFSGFFourE6OriginalMiddleFactors
open CFSGFFourE6SimpleGeneratedParameters CFSGFFourE6OriginalSimpleParameters
open CFSGFFourE6GeneratedOriginalProjection CFSGTwistedE6GeckRelativeRootGenerated
open CFSGTwistedE6GeckRootGeneratedPGroup CFSGTwistedE6GeckDiagramCovariance
open CFSGE6GeckMiddlePairedCollecting CFSGE6GeckMiddleAThreeCollecting
open CFSGE6GeckMiddleFactorInjective CFSGE6GeckMiddleRootDegrees
open CFSGE6GeckSignedSimpleParameters CFSGE6GeckRelativeSimpleHom
open CFSGSerreQuadraticMatrix CFSGSerreQuadraticWeylWord
open CFSGTwistedE6RelativeWeylOrbits CFSG.Models.Chevalley

def middleLongInGenerated (K : Type) [Field K] (a : K) : fixedRootGenerated K (RingEquiv.refl K) :=
  simpleWeylInGenerated K 1*simpleInGenerated K false 2 (Multiplicative.ofAdd a)*
    (simpleWeylInGenerated K 1)⁻¹

def middleShortInGenerated (K : Type) [Field K] (a : K) : fixedRootGenerated K (RingEquiv.refl K) :=
  simpleWeylInGenerated K 2*simpleInGenerated K false 1 (Multiplicative.ofAdd a)*
    (simpleWeylInGenerated K 2)⁻¹

theorem middleLongInGenerated_val (K : Type) [Field K] (a : K) :
    (middleLongInGenerated K a).val=highestMiddle K a := by
  have hw : (simpleWeylInGenerated K 1).val=canonicalWeyl rawData K 2*canonicalWeyl rawData K 4 := by
    rw [simpleWeylInGenerated_val]
    simp [orbitWord,canonicalWord]
  change (simpleWeylInGenerated K 1).val*(simpleInGenerated K false 2 (Multiplicative.ofAdd a)).val*
    (simpleWeylInGenerated K 1).val⁻¹=_
  rw [simpleInGenerated_val,hw]
  rfl

theorem middleShortInGenerated_val (K : Type) [Field K] (a : K) :
    (middleShortInGenerated K a).val=middlePair K (RingEquiv.refl K) a := by
  have hw : (simpleWeylInGenerated K 2).val=canonicalWeyl rawData K 3 := by
    rw [simpleWeylInGenerated_val]
    simp [orbitWord,canonicalWord]
  change (simpleWeylInGenerated K 2).val*(simpleInGenerated K false 1 (Multiplicative.ofAdd a)).val*
    (simpleWeylInGenerated K 2).val⁻¹=_
  rw [simpleInGenerated_val,hw]
  rfl

def middleLongOriginalHom (K : Type) [Field K] [Finite K]
    [IsSimpleGroup (Projective CartanMatrix.F₄ K)] : Multiplicative K→*Projective CartanMatrix.F₄ K :=
  (MulAut.conj (generatedToOriginal K (simpleWeylInGenerated K 1))).toMonoidHom.comp
    (originalSimpleHom K false 2)

def middleShortOriginalHom (K : Type) [Field K] [Finite K]
    [IsSimpleGroup (Projective CartanMatrix.F₄ K)] : Multiplicative K→*Projective CartanMatrix.F₄ K :=
  (MulAut.conj (generatedToOriginal K (simpleWeylInGenerated K 2))).toMonoidHom.comp
    (originalSimpleHom K false 1)

theorem middleLongInGenerated_original (K : Type) [Field K] [Finite K]
    [IsSimpleGroup (Projective CartanMatrix.F₄ K)] (a : K) :
    generatedToOriginal K (middleLongInGenerated K a)=middleLongOriginalHom K (Multiplicative.ofAdd a) := by
  simp only [middleLongInGenerated,map_mul,map_inv,simpleInGenerated_original]
  rfl

theorem middleShortInGenerated_original (K : Type) [Field K] [Finite K]
    [IsSimpleGroup (Projective CartanMatrix.F₄ K)] (a : K) :
    generatedToOriginal K (middleShortInGenerated K a)=middleShortOriginalHom K (Multiplicative.ofAdd a) := by
  simp only [middleShortInGenerated,map_mul,map_inv,simpleInGenerated_original]
  rfl

theorem middleLongInGenerated_mem_positive (K : Type) [Field K] (a : K) :
    middleLongInGenerated K a∈rootPart K (RingEquiv.refl K) false := by
  constructor
  · change (middleLongInGenerated K a).val∈CFSGTwistedE6GeckPositiveTwist.Positive K
    rw [middleLongInGenerated_val]
    exact highestMiddle_mem_positive K a
  · exact fixedRootGenerated_le_fixed K (RingEquiv.refl K) (middleLongInGenerated K a).property

theorem middleShortInGenerated_mem_positive (K : Type) [Field K] (a : K) :
    middleShortInGenerated K a∈rootPart K (RingEquiv.refl K) false := by
  constructor
  · change (middleShortInGenerated K a).val∈CFSGTwistedE6GeckPositiveTwist.Positive K
    rw [middleShortInGenerated_val]
    exact middlePair_mem_positive K (RingEquiv.refl K) a
  · exact fixedRootGenerated_le_fixed K (RingEquiv.refl K) (middleShortInGenerated K a).property

theorem original_middleFactor_snd_eq (K : Type) [Field K] [Finite K]
    (p : ℕ) [Fact p.Prime] [CharP K p] [IsSimpleGroup (Projective CartanMatrix.F₄ K)]
    (r r' a a' : K)
    (he : middleLongOriginalHom K (Multiplicative.ofAdd r)*middleShortOriginalHom K (Multiplicative.ofAdd a)=
      middleLongOriginalHom K (Multiplicative.ofAdd r')*middleShortOriginalHom K (Multiplicative.ofAdd a')) : a=a' := by
  let U := rootPart K (RingEquiv.refl K) false
  let x : U := ⟨middleLongInGenerated K r*middleShortInGenerated K a,
    U.mul_mem (middleLongInGenerated_mem_positive K r) (middleShortInGenerated_mem_positive K a)⟩
  let y : U := ⟨middleLongInGenerated K r'*middleShortInGenerated K a',
    U.mul_mem (middleLongInGenerated_mem_positive K r') (middleShortInGenerated_mem_positive K a')⟩
  have hproj : generatedToOriginal K x.val=generatedToOriginal K y.val := by
    change generatedToOriginal K (middleLongInGenerated K r*middleShortInGenerated K a)=
      generatedToOriginal K (middleLongInGenerated K r'*middleShortInGenerated K a')
    simpa only [map_mul,middleLongInGenerated_original,middleShortInGenerated_original] using he
  have hxy : x=y := rootPart_positive_original_injective K p hproj
  have hraw := congrArg (fun z : U=>z.val.val) hxy
  change (middleLongInGenerated K r).val*(middleShortInGenerated K a).val=
    (middleLongInGenerated K r').val*(middleShortInGenerated K a').val at hraw
  rw [middleLongInGenerated_val,middleShortInGenerated_val,
    middleLongInGenerated_val,middleShortInGenerated_val] at hraw
  exact middleFactor_snd_eq K (RingEquiv.refl K) r r' a a' hraw

theorem original_middle_commutator (K : Type) [Field K] [Finite K]
    [IsSimpleGroup (Projective CartanMatrix.F₄ K)] (a b : K) :
    ⁅originalSimpleHom K false 1 (Multiplicative.ofAdd a),
      originalSimpleHom K false 2 (Multiplicative.ofAdd b)⁆=
      middleLongOriginalHom K (Multiplicative.ofAdd (a*a*b))*
        middleShortOriginalHom K (Multiplicative.ofAdd (-(a*b))) := by
  have hJ : ⁅simpleInGenerated K false 1 (Multiplicative.ofAdd a),
      simpleInGenerated K false 2 (Multiplicative.ofAdd b)⁆=
    middleLongInGenerated K (a*a*b)*middleShortInGenerated K (-(a*b)) := by
    apply Subtype.ext
    change ⁅(simpleInGenerated K false 1 (Multiplicative.ofAdd a)).val,
      (simpleInGenerated K false 2 (Multiplicative.ofAdd b)).val⁆=
      (middleLongInGenerated K (a*a*b)).val*(middleShortInGenerated K (-(a*b))).val
    rw [simpleInGenerated_val,simpleInGenerated_val,middleLongInGenerated_val,middleShortInGenerated_val]
    exact middle_paired_commutator K (RingEquiv.refl K) a b rfl
  simpa only [map_commutatorElement,map_mul,simpleInGenerated_original,
    middleLongInGenerated_original,middleShortInGenerated_original] using congrArg (generatedToOriginal K) hJ

end SymmetricSubgroupAsymptotics.CFSGFFourE6OriginalMiddleFactors
