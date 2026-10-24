import SymmetricSubgroupAsymptotics.CFSGReeFFourOuterAdjointTriple
import SymmetricSubgroupAsymptotics.CFSGReeFFourOuterTorusReflection
import SymmetricSubgroupAsymptotics.CFSGNormTwoGeckSelfRootConjugation

/-! The genuine original outer Weyl element conjugates every positive
outer parameter to its signed negative parameter. The proof uses the
three actual orthogonal E6 factors and their integral self-root identities. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics.CFSGReeFFourOuterSignedConjugation
open CFSGReeFFourOuterAdjointTriple CFSGReeFFourOuterUnipotentGeneration
open CFSGReeFFourFieldParameters CFSGReeFFourOuterTorusReflection
open CFSGReeFFourRelativeWeylRawWords CFSGReeFFourRelativeSimpleWeyl
open CFSGFFourOriginalMiddleWords CFSGTwistedE6GeckDiagramCovariance
open CFSGSerreQuadraticMatrix CFSGSerreQuadraticWeylWord
open CFSGNormTwoGeckOrthogonalWeyl CFSGNormTwoGeckSelfRootConjugation
open CFSGNormTwoGeckIntegralWord CFSGNormTwoGeckWeylWordDegree
open CFSGExceptionalNormTwoBases CFSGExceptionalCartanPositiveDefinite
open CFSGNormTwoRootPairing CFSGReeFFourFixedModelEquivalence
local notation "A" => CartanMatrix.E₆
local notation "hs" => CartanMatrix.E₆_transpose
local notation "hp" => E6_positive_definite
local notation "R" => CFSGTwistedE6GeckDiagramCovariance.rawData
local instance : DecidableEq (Roots A) := Classical.decEq _

private theorem commute_conjugate {G : Type*} [Group G] {w x : G} (h : Commute w x) :
    w*x*w⁻¹=x := by rw [h.eq,mul_assoc,mul_inv_cancel,mul_one]

private theorem conjugate_three {G : Type*} [Group G] (w0 w1 w2 x0 x1 x2 y0 y1 y2 : G)
    (h0 : w0*x0*w0⁻¹=y0) (h1 : w1*x1*w1⁻¹=y1) (h2 : w2*x2*w2⁻¹=y2)
    (h10 : Commute w1 x0) (h20 : Commute w2 x0) (h21 : Commute w2 x1)
    (h01 : Commute w0 y1) (h02 : Commute w0 y2) (h12 : Commute w1 y2) :
    (w0*w1*w2)*(x0*x1*x2)*(w0*w1*w2)⁻¹=y0*y1*y2 := by
  have hA : (w0*w1*w2)*x0*(w0*w1*w2)⁻¹=y0 := by
    calc
      _=w0*(w1*(w2*x0*w2⁻¹)*w1⁻¹)*w0⁻¹ := by group
      _=y0 := by rw [commute_conjugate h20,commute_conjugate h10,h0]
  have hB : (w0*w1*w2)*x1*(w0*w1*w2)⁻¹=y1 := by
    calc
      _=w0*(w1*(w2*x1*w2⁻¹)*w1⁻¹)*w0⁻¹ := by group
      _=y1 := by rw [commute_conjugate h21,h1,commute_conjugate h01]
  have hC : (w0*w1*w2)*x2*(w0*w1*w2)⁻¹=y2 := by
    calc
      _=w0*(w1*(w2*x2*w2⁻¹)*w1⁻¹)*w0⁻¹ := by group
      _=y2 := by rw [h2,commute_conjugate h12,commute_conjugate h02]
  calc
    _=((w0*w1*w2)*x0*(w0*w1*w2)⁻¹)*((w0*w1*w2)*x1*(w0*w1*w2)⁻¹)*
      ((w0*w1*w2)*x2*(w0*w1*w2)⁻¹) := by group
    _=y0*y1*y2 := by rw [hA,hB,hC]

theorem model_outer_conjugates_parameter (m : ℕ) (a : Field m) :
    outerRelativeWeyl m*signedOuterWord m false a*(outerRelativeWeyl m)⁻¹=
      signedOuterWord m true a := by
  apply rawHom_injective (Field m)
  simp only [map_mul,map_inv,rawHom_signedOuterWord]
  have hW : rawHom (Field m) (outerRelativeWeyl m)=
      canonicalWeyl R (Field m) 0*canonicalWeyl R (Field m) 5*canonicalWeyl R (Field m) 1 := by
    simpa only [word_eq_canonicalWord,canonicalWord,mul_one,mul_assoc] using rawHom_outerRelativeWeyl m
  rw [hW]
  exact conjugate_three
    (canonicalWeyl R (Field m) 0) (canonicalWeyl R (Field m) 5) (canonicalWeyl R (Field m) 1)
    (canonicalRoot R (Field m) false 0 a) (canonicalRoot R (Field m) false 5 a)
    (canonicalRoot R (Field m) false 1 (alpha m a))
    (canonicalRoot R (Field m) true 0 a) (canonicalRoot R (Field m) true 5 a)
    (canonicalRoot R (Field m) true 1 (alpha m a))
    (by simpa only [CharTwo.neg_eq] using self_root_word A hs hp E6Base E6Index (Field m) 0 a)
    (by simpa only [CharTwo.neg_eq] using self_root_word A hs hp E6Base E6Index (Field m) 5 a)
    (by simpa only [CharTwo.neg_eq] using self_root_word A hs hp E6Base E6Index (Field m) 1 (alpha m a))
    (orthogonal_weyl_root A hs hp E6Base E6Index (Field m) 5 0 (by rw [E6_cartan];decide) false a)
    (orthogonal_weyl_root A hs hp E6Base E6Index (Field m) 1 0 (by rw [E6_cartan];decide) false a)
    (orthogonal_weyl_root A hs hp E6Base E6Index (Field m) 1 5 (by rw [E6_cartan];decide) false a)
    (orthogonal_weyl_root A hs hp E6Base E6Index (Field m) 0 5 (by rw [E6_cartan];decide) true a)
    (orthogonal_weyl_root A hs hp E6Base E6Index (Field m) 0 1 (by rw [E6_cartan];decide) true (alpha m a))
    (orthogonal_weyl_root A hs hp E6Base E6Index (Field m) 5 1 (by rw [E6_cartan];decide) true (alpha m a))

theorem fixed_outer_conjugates_parameter (m : ℕ) (a : Field m) :
    outerFixedReflection m*fixedSignedOuter m false a*(outerFixedReflection m)⁻¹=
      fixedSignedOuter m true a :=
  Subtype.ext (model_outer_conjugates_parameter m a)

end SymmetricSubgroupAsymptotics.CFSGReeFFourOuterSignedConjugation
