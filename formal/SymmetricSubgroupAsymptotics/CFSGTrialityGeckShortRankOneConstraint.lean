import SymmetricSubgroupAsymptotics.CFSGTrialityGeckShortAdjointTriple
import SymmetricSubgroupAsymptotics.CFSGQuadraticRankOneIntertwiner

/-! An actual short rank-one word intertwining a positive short element
with a nonidentity negative one has the forced inverse parameters.
The original Geck adjoint triple detects this in every characteristic. -/
set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped Matrix
namespace SymmetricSubgroupAsymptotics.CFSGTrialityGeckShortRankOneConstraint
open CFSGTrialityD4NormTwo CFSGTrialityGeckDiagramCovariance
open CFSGTrialityGeckFixedRootWords CFSGTrialityGeckShortAdjointTriple
open CFSGNormTwoGeckParameterTripleColumns CFSGQuadraticRankOneIntertwiner
local instance : DecidableEq (CFSGNormTwoRootPairing.Roots (CartanMatrix.D 4)) := Classical.decEq _
local notation "A" => CartanMatrix.D 4
local notation "hs" => CartanMatrix.D_transpose 4
local notation "hp" => D4_positive_definite

def shortOperator (K : Type) [Field K] (sigma : K≃+*K) (neg : Bool) (t : K) :
    Module.End K (GeckIndex→K) :=
  Matrix.toLinAlgEquiv' (shortOrbit K sigma neg t : Matrix GeckIndex GeckIndex K)

private theorem short_triple (K : Type) [Field K] (sigma : K≃+*K) :
    (∀a,shortOperator K sigma false a (tripleCartan K)=
      tripleCartan K+(2*a) • triplePositive K)∧
    (∀a,shortOperator K sigma false a (triplePositive K)=triplePositive K)∧
    (∀a,shortOperator K sigma false a (tripleNegative K)=
      tripleNegative K+a • tripleCartan K+a^2 • triplePositive K)∧
    (∀a,shortOperator K sigma true a (tripleCartan K)=
      tripleCartan K+(2*a) • tripleNegative K)∧
    (∀a,shortOperator K sigma true a (triplePositive K)=
      triplePositive K+a • tripleCartan K+a^2 • tripleNegative K)∧
    (∀a,shortOperator K sigma true a (tripleNegative K)=tripleNegative K) := by
  refine ⟨?_,?_,?_,?_,?_,?_⟩
  · intro a
    exact (shortOrbit_triple_restriction K sigma false a).1.trans
      (positive_cartan A hs hp Base Index K 0 a)
  · intro a
    exact (shortOrbit_triple_restriction K sigma false a).2.1.trans
      (positive_positive A hs hp Base Index K 0 a)
  · intro a
    exact (shortOrbit_triple_restriction K sigma false a).2.2.trans
      (positive_negative A hs hp Base Index K 0 a)
  · intro a
    exact (shortOrbit_triple_restriction K sigma true a).1.trans
      (negative_cartan A hs hp Base Index K 0 a)
  · intro a
    exact (shortOrbit_triple_restriction K sigma true a).2.1.trans
      (negative_positive A hs hp Base Index K 0 a)
  · intro a
    exact (shortOrbit_triple_restriction K sigma true a).2.2.trans
      (negative_negative A hs hp Base Index K 0 a)

theorem short_word_inverse_constraint (K : Type) [Field K] (sigma : K≃+*K)
    (a b t s : K) (hs0 : s≠0)
    (hinter : (shortOrbit K sigma false a*shortOrbit K sigma true b*shortOrbit K sigma false a)*
        shortOrbit K sigma false t=
      shortOrbit K sigma true s*
        (shortOrbit K sigma false a*shortOrbit K sigma true b*shortOrbit K sigma false a)) :
    1+a*b=0 := by
  let U := shortOperator K sigma false
  let V := shortOperator K sigma true
  let l : (GeckIndex→K)→ₗ[K]K := LinearMap.proj (Sum.inl (Index 0))
  have hlu : l (tripleCartan K)=1 := by
    change (Pi.single (Sum.inl (Index 0)) (1:K) : GeckIndex→K) (Sum.inl (Index 0))=1
    simp only [Pi.single_eq_same]
  have hlp : l (triplePositive K)=0 := by
    change (Pi.single (Sum.inr (Index 0 : CFSGNormTwoRootPairing.Roots A)) (1:K) :
      GeckIndex→K) (Sum.inl (Index 0))=0
    simp only [Pi.single_apply,Sum.inl_ne_inr,Sum.inr_ne_inl,if_false]
  have hlm : l (tripleNegative K)=0 := by
    change (Pi.single (Sum.inr (CFSGNormTwoGeckColumns.negativeIndex A hs hp (Index 0))) (1:K) :
      GeckIndex→K) (Sum.inl (Index 0))=0
    simp only [Pi.single_apply,Sum.inl_ne_inr,Sum.inr_ne_inl,if_false]
  have he := congrArg (fun z : (Matrix GeckIndex GeckIndex K)ˣ=>
    Matrix.toLinAlgEquiv' (z : Matrix GeckIndex GeckIndex K)) hinter
  simp only [Units.val_mul,map_mul] at he
  change tripleWord U V a b*U t=V s*tripleWord U V a b at he
  obtain ⟨hUu,hUp,hUm,hVu,hVp,hVm⟩ := short_triple K sigma
  exact one_add_mul_eq_zero_of_intertwines U V (tripleCartan K) (triplePositive K)
    (tripleNegative K) hUu hUp hUm hVu hVp hVm l hlu hlp hlm a b t s hs0 he

end SymmetricSubgroupAsymptotics.CFSGTrialityGeckShortRankOneConstraint
