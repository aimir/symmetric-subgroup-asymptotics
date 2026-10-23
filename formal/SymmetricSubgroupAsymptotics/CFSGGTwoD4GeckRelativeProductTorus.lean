import SymmetricSubgroupAsymptotics.CFSGGTwoD4GeckProductTorus
import SymmetricSubgroupAsymptotics.CFSGGTwoD4GeckSimpleParameters
import SymmetricSubgroupAsymptotics.CFSGNormTwoCoordinateRootLineNormalizers

/-! The folded scalar tuples give actual words in J(K,id). The two
rank-one word families construct the membership witness, and the SAME
raw diagonal torus hom supplies multiplicativity and both U/V normalizers. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics.CFSGGTwoD4GeckRelativeProductTorus
open CFSGGTwoD4GeckProductTorus CFSGGTwoD4GeckScalarTuple
open CFSGGTwoD4GeckSimpleParameters CFSGTrialityGeckRelativeRootGenerated
open CFSGTrialityGeckRootGeneratedPGroup CFSGTrialityGeckDiagramCovariance
open CFSGTrialityGeckMatrixTwist CFSGTrialityD4NormTwo
open CFSGTrialityGeckShortTorusConjugation CFSGTrialityGeckShortParameterWeyl
open CFSGNormTwoGeckParameterizedTorus CFSGNormTwoGeckParameterizedWeyl
open CFSGNormTwoCoordinateRootLineNormalizers CFSGSerreQuadraticMatrix
open CFSGCentralTwistedCommutatorLift
variable (K : Type) [Field K] [Finite K]
local notation "J" => fixedRootGenerated K (RingEquiv.refl K)

def relativeWeylWord (a : Bool) (t : Kˣ) : J :=
  simpleGeneratedHom K false a (Multiplicative.ofAdd (t : K))*
    simpleGeneratedHom K true a (Multiplicative.ofAdd (-(t : K)⁻¹))*
    simpleGeneratedHom K false a (Multiplicative.ofAdd (t : K))

def relativeTorusNode (a : Bool) (t : Kˣ) : J :=
  relativeWeylWord K a t*(relativeWeylWord K a 1)⁻¹

theorem relativeTorusNode_short_val (t : Kˣ) :
    (relativeTorusNode K false t).val=shortTorusWord K (RingEquiv.refl K) t := by
  simp only [relativeTorusNode,relativeWeylWord,Subgroup.coe_mul,Subgroup.coe_inv,
    simpleGeneratedHom_val]
  rfl

theorem relativeTorusNode_long_val (t : Kˣ) :
    (relativeTorusNode K true t).val=
      parameterTorus (CartanMatrix.D 4) (CartanMatrix.D_transpose 4)
        D4_positive_definite Base Index K 1 t := by
  simp only [relativeTorusNode,relativeWeylWord,Subgroup.coe_mul,Subgroup.coe_inv,
    simpleGeneratedHom_val]
  rfl

def relativeTorusWord (x : Fin 2→Kˣ) : J :=
  relativeTorusNode K false (x 0)*relativeTorusNode K true (x 1)

theorem relativeTorusWord_val (x : Fin 2→Kˣ) :
    (relativeTorusWord K x).val=rawProductTorus K (scalarTupleHom x) := by
  change (relativeTorusNode K false (x 0)).val*(relativeTorusNode K true (x 1)).val=_
  rw [relativeTorusNode_short_val,relativeTorusNode_long_val]
  exact (rawProductTorus_orbit_factors K x).symm

def relativeProductTorus : (Fin 2→Kˣ)→*J :=
  ((rawProductTorus K).comp scalarTupleHom).codRestrict J (fun x=>by
    change rawProductTorus K (scalarTupleHom x)∈J
    rw [←relativeTorusWord_val K x]
    exact (relativeTorusWord K x).property)

@[simp] theorem relativeProductTorus_val (x : Fin 2→Kˣ) :
    (relativeProductTorus K x).val=rawProductTorus K (scalarTupleHom x) := rfl

theorem relativeProductTorus_normalizes (x : Fin 2→Kˣ) (neg : Bool) :
    relativeProductTorus K x∈Subgroup.normalizer
      (rootPart K (RingEquiv.refl K) neg : Set J) := by
  let t := relativeProductTorus K x
  have ht : t.val∈Subgroup.normalizer
      (signedFixed K (RingEquiv.refl K) neg : Set (Matrix GeckIndex GeckIndex K)ˣ) := by
    apply Subgroup.inf_normalizer_le_normalizer_inf
    refine ⟨?_,?_⟩
    · exact torusGroup_normalizes (CartanMatrix.D 4) (CartanMatrix.D_diag 4)
        (CartanMatrix.D_transpose 4) D4_positive_definite (CartanMatrix.D_off_diag_nonpos 4) K neg
        (rawProductTorus_mem_torus K (scalarTupleHom x))
    · exact (fixedSubgroup (unitTwist K (RingEquiv.refl K))).le_normalizer
        (fixedRootGenerated_le_fixed K (RingEquiv.refl K) t.property)
  let inclusion : fixedRootGenerated K (RingEquiv.refl K)→*
      (Matrix GeckIndex GeckIndex K)ˣ := (fixedRootGenerated K (RingEquiv.refl K)).subtype
  change relativeProductTorus K x∈Subgroup.normalizer
    ((signedFixed K (RingEquiv.refl K) neg).comap inclusion : Set J)
  apply Subgroup.le_normalizer_comap inclusion
  exact ht

end SymmetricSubgroupAsymptotics.CFSGGTwoD4GeckRelativeProductTorus
