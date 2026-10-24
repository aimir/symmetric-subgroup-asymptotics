import SymmetricSubgroupAsymptotics.CFSGReeFFourOuterAdjointTriple
import SymmetricSubgroupAsymptotics.CFSGQuadraticRankOneIntertwiner

/-! The genuine signed original outer words satisfy the inverse-parameter
constraint, detected by their original coefficient-one adjoint triple.
No rank-one group identification or automorphism lift is supplied. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Matrix Classical
namespace SymmetricSubgroupAsymptotics.CFSGReeFFourOuterRankOneConstraint
open CFSGReeFFourOuterAdjointTriple CFSGReeFFourFieldParameters
open CFSGReeFFourOuterUnipotentGeneration CFSGFFourOriginalMiddleWords
open CFSGTwistedE6GeckDiagramCovariance CFSGTwistedE6WeylChamber
open CFSGNormTwoGeckParameterTripleColumns CFSGQuadraticRankOneIntertwiner
open CFSGExceptionalNormTwoBases CFSGExceptionalCartanPositiveDefinite
open CFSGNormTwoRootPairing CFSGNormTwoGeckColumns CFSG.Models.Chevalley
local notation "A" => CartanMatrix.E₆
local notation "hs" => CartanMatrix.E₆_transpose
local notation "hp" => E6_positive_definite
local instance : DecidableEq (Roots A) := Classical.decEq _

def outerOperator (m : ℕ) (neg : Bool) (t : Field m) :
    Module.End (Field m) (GeckIndex→Field m) :=
  Matrix.toLinAlgEquiv' (rawSignedOuter m neg t : Matrix GeckIndex GeckIndex (Field m))

private theorem outer_triple (m : ℕ) :
    (∀a,outerOperator m false a (tripleCartan m)=tripleCartan m+(2*a) • triplePositive m) ∧
    (∀a,outerOperator m false a (triplePositive m)=triplePositive m) ∧
    (∀a,outerOperator m false a (tripleNegative m)=
      tripleNegative m+a • tripleCartan m+a^2 • triplePositive m) ∧
    (∀a,outerOperator m true a (tripleCartan m)=tripleCartan m+(2*a) • tripleNegative m) ∧
    (∀a,outerOperator m true a (triplePositive m)=
      triplePositive m+a • tripleCartan m+a^2 • tripleNegative m) ∧
    (∀a,outerOperator m true a (tripleNegative m)=tripleNegative m) := by
  refine ⟨?_,?_,?_,?_,?_,?_⟩
  · intro a
    exact (rawSignedOuter_triple_restriction m false a).1.trans
      (positive_cartan A hs hp E6Base E6Index (Field m) 0 a)
  · intro a
    exact (rawSignedOuter_triple_restriction m false a).2.1.trans
      (positive_positive A hs hp E6Base E6Index (Field m) 0 a)
  · intro a
    exact (rawSignedOuter_triple_restriction m false a).2.2.trans
      (positive_negative A hs hp E6Base E6Index (Field m) 0 a)
  · intro a
    exact (rawSignedOuter_triple_restriction m true a).1.trans
      (negative_cartan A hs hp E6Base E6Index (Field m) 0 a)
  · intro a
    exact (rawSignedOuter_triple_restriction m true a).2.1.trans
      (negative_positive A hs hp E6Base E6Index (Field m) 0 a)
  · intro a
    exact (rawSignedOuter_triple_restriction m true a).2.2.trans
      (negative_negative A hs hp E6Base E6Index (Field m) 0 a)

theorem raw_outer_inverse_constraint (m : ℕ) (a b t s : Field m) (hs0 : s≠0)
    (hinter : (rawSignedOuter m false a*rawSignedOuter m true b*rawSignedOuter m false a)*
        rawSignedOuter m false t=rawSignedOuter m true s*
          (rawSignedOuter m false a*rawSignedOuter m true b*rawSignedOuter m false a)) :
    1+a*b=0 := by
  let U := outerOperator m false
  let V := outerOperator m true
  let l : (GeckIndex→Field m)→ₗ[Field m]Field m := LinearMap.proj (Sum.inl (E6Index 0))
  have hlu : l (tripleCartan m)=1 := by
    change (Pi.single (Sum.inl (E6Index 0)) (1 : Field m) : GeckIndex→Field m)
      (Sum.inl (E6Index 0))=1
    simp only [Pi.single_eq_same]
  have hlp : l (triplePositive m)=0 := by
    change (Pi.single (Sum.inr (E6Index 0 : Roots A)) (1 : Field m) : GeckIndex→Field m)
      (Sum.inl (E6Index 0))=0
    simp only [Pi.single_apply,Sum.inl_ne_inr,Sum.inr_ne_inl,if_false]
  have hlm : l (tripleNegative m)=0 := by
    change (Pi.single (Sum.inr (negativeIndex A hs hp (E6Index 0))) (1 : Field m) :
      GeckIndex→Field m) (Sum.inl (E6Index 0))=0
    simp only [Pi.single_apply,Sum.inl_ne_inr,Sum.inr_ne_inl,if_false]
  have he := congrArg (fun z : (Matrix GeckIndex GeckIndex (Field m))ˣ=>
    Matrix.toLinAlgEquiv' (z : Matrix GeckIndex GeckIndex (Field m))) hinter
  simp only [Units.val_mul,map_mul] at he
  change tripleWord U V a b*U t=V s*tripleWord U V a b at he
  obtain ⟨hUu,hUp,hUm,hVu,hVp,hVm⟩ := outer_triple m
  exact one_add_mul_eq_zero_of_intertwines U V (tripleCartan m) (triplePositive m)
    (tripleNegative m) hUu hUp hUm hVu hVp hVm l hlu hlp hlm a b t s hs0 he

theorem model_outer_inverse_constraint (m : ℕ) (a b t s : Field m) (hs0 : s≠0)
    (hinter : (signedOuterWord m false a*signedOuterWord m true b*signedOuterWord m false a)*
        signedOuterWord m false t=signedOuterWord m true s*
          (signedOuterWord m false a*signedOuterWord m true b*signedOuterWord m false a)) :
    1+a*b=0 := by
  have he := congrArg (rawHom (Field m)) hinter
  simp only [map_mul,rawHom_signedOuterWord] at he
  exact raw_outer_inverse_constraint m a b t s hs0 he

end SymmetricSubgroupAsymptotics.CFSGReeFFourOuterRankOneConstraint
