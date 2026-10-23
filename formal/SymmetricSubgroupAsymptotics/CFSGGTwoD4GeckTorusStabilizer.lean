import SymmetricSubgroupAsymptotics.CFSGGTwoD4GeckStabilizerParameters
import SymmetricSubgroupAsymptotics.CFSGGTwoD4GeckOriginalProductTorusAction
import SymmetricSubgroupAsymptotics.CFSGSemilinearRootCosetIndex
import SymmetricSubgroupAsymptotics.PrimitiveSocleRawSimpleIndex

/-! Literal original G2 inner tori lie in the signed-label kernel and
realize the surjective two-scalar Cartan map. Once the actual common-field
and faithful-parameter dependencies are checked, their range has index
at most the actual field-automorphism count. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGGTwoD4GeckTorusStabilizer
open CFSGGTwoD4GeckOriginalSimpleStabilizer CFSGGTwoD4GeckStabilizerParameters
open CFSGGTwoD4GeckOriginalProductTorusAction CFSGGTwoD4GeckProductTorusParameters
open CFSGGTwoD4GeckOriginalSimpleParameters CFSGGTwoD4GeckOriginalProjection
open CFSGGTwoD4GeckOriginalOppositeAlignment CFSGGTwoD4GeckScalarTorus
open CFSGTrialityGeckRootGeneratedPGroup CFSGTrialityGeckRelativeRootGenerated
open CFSGSemilinearRootCosetIndex CFSGIntegerMatrixPowerHom CFSG.Models.Chevalley
variable (K : Type) [Field K] [Finite K]
    [IsSimpleGroup (Projective CartanMatrix.G₂ K)]

private theorem product_torus_rootPart_map (x : Fin 2→Kˣ) (neg : Bool) :
    ((rootPart K (RingEquiv.refl K) neg).map (generatedToOriginal K)).map
      (MulAut.conj (originalProductTorus K x)).toMonoidHom=
      (rootPart K (RingEquiv.refl K) neg).map (generatedToOriginal K) := by
  apply SetLike.coe_injective
  exact Subgroup.mem_normalizer_iff_conj_image_eq.mp (originalProductTorus_normalizes K x neg)

variable (p : ℕ) [Fact p.Prime] [CharP K p]

def productTorusPairHom : (Fin 2→Kˣ)→*pairStabilizer K p :=
  (MulAut.conj.comp (originalProductTorus K)).codRestrict (pairStabilizer K p) (by
    intro x neg
    cases neg
    · change (originalPositiveSylow K p : Subgroup (Projective CartanMatrix.G₂ K)).map
        (MulAut.conj (originalProductTorus K x)).toMonoidHom=_
      rw [originalPositiveSylow_coe]
      exact product_torus_rootPart_map K x false
    · exact product_torus_rootPart_map K x true)

def productTorusSimpleHom : (Fin 2→Kˣ)→*simpleStabilizer K p :=
  (productTorusPairHom K p).codRestrict (simpleStabilizer K p) (by
    intro x z
    exact originalProductTorus_simple_range K x z.1 z.2)

theorem product_torus_lift_action (x : Fin 2→Kˣ) (i : Fin 2) (a : K) :
    simpleStabilizerAction K p (productTorusSimpleHom K p x) (positiveParameter K i a)=
      positiveParameter K i ((powerHom (G:=Kˣ) relativeCartan x i : K)*a) := by
  change originalProductTorus K x*positiveParameter K i a*(originalProductTorus K x)⁻¹=_
  have he := originalProductTorus_simple_action K x false (axisBool i) a
  simpa only [positiveParameter,parameterScalar_val,Bool.false_eq_true,if_false,
    axisIndex_axisBool,mul_comm] using he

theorem product_torus_inner (x : (productTorusSimpleHom K p).range) :
    (x.val.val.val : MulAut (Projective CartanMatrix.G₂ K))∈
      PrimitiveSocleRawStructure.Inner (Projective CartanMatrix.G₂ K) := by
  obtain ⟨t,ht⟩ := x.property
  refine ⟨originalProductTorus K t,?_⟩
  exact congrArg (fun f : simpleStabilizer K p=>
    (f.val.val : MulAut (Projective CartanMatrix.G₂ K))) ht

theorem product_torus_index_le :
    (productTorusSimpleHom K p).range.index≤Nat.card (RingAut K) := by
  have hi := scalar_lift_index_le (positiveParameter K) (simpleStabilizerAction K p)
    (parameters_faithful K p) (semilinear_parameters K p)
    (productTorusSimpleHom K p) (powerHom (G:=Kˣ) relativeCartan) (product_torus_lift_action K p)
  simpa only [range_index_eq_one,one_mul] using hi

end SymmetricSubgroupAsymptotics.CFSGGTwoD4GeckTorusStabilizer
