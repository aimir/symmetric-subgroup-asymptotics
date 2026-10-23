import SymmetricSubgroupAsymptotics.CFSGTrialityD4FiniteWeylMenu
import SymmetricSubgroupAsymptotics.CFSGTrialityGeckRelativeBruhatCover
import SymmetricSubgroupAsymptotics.CFSGTrialityGeckCentralTwistedCellFactors
import SymmetricSubgroupAsymptotics.CFSGTrialityGeckFixedPairNormalizer
import SymmetricSubgroupAsymptotics.CFSGFixedSubgroupConjugation

/-! A genuinely fixed finite-menu Bruhat cover of literal J.
All three variable factors are genuinely fixed and belong to J;
the middle factor is the actual opposed-pair normalizer, not assumed T. -/
set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics.CFSGTrialityGeckFiniteFixedBruhatCover
open CFSGTrialityD4NormTwo CFSGTrialityGeckDiagramCovariance
open CFSGTrialityD4FiniteWeylMenu CFSGTrialityGeckRelativeBruhatCover
open CFSGTrialityGeckCentralTwistedCellFactors CFSGTrialityGeckFixedPairNormalizer
open CFSGTrialityGeckRelativeRootGenerated CFSGTrialityGeckNormalizerEnvelope
open CFSGTrialityGeckSourceWordAction CFSGTrialityGeckNormalizerEnvelopeTwist
open CFSGTrialityGeckFixedRangePreimage
open CFSGTrialityGeckBruhatCellFactors CFSGTrialityRelativeWordLanguage
open CFSGTrialityGeckMatrixTwist CFSGTrialityGeckPositiveTwist
open CFSGNormTwoGeckWeylWordDegree CFSGNormTwoGeckIntegralWord
open CFSGFixedSubgroupConjugation

def menuMatrix (K:Type) [Field K] (i:Menu) : (Matrix GeckIndex GeckIndex K)ˣ :=
  wordUnit (CartanMatrix.D 4) (CartanMatrix.D_transpose 4) D4_positive_definite
    Base Index K (expandRelative (menuWord i))

theorem menuMatrix_mem_generated (K:Type) [Field K] (sigma:K≃+*K) (i:Menu) :
    menuMatrix K i∈fixedRootGenerated K sigma := relativeWord_mem_generated K sigma _

theorem fixed_diagonal_mem_pair (K:Type) [Field K] (sigma:K≃+*K)
    (d:(Matrix GeckIndex GeckIndex K)ˣ) (hd:d∈diagonalNormalizer K)
    (hJ:d∈fixedRootGenerated K sigma) : d∈pairNormalizer K sigma := by
  have hf : unitTwist K sigma d=d := fixedRootGenerated_le_fixed K sigma hJ
  exact ⟨⟨normalizes_inf_fixed (unitTwist K sigma) (Positive K) d hf hd.1.1,
    normalizes_inf_fixed (unitTwist K sigma) (Negative K) d hf hd.1.2⟩,hJ⟩

theorem exists_finite_fixed_cell (K:Type) [Field K] [Finite K] (sigma:K≃+*K)
    (g:(Matrix GeckIndex GeckIndex K)ˣ) (hg:g∈fixedRootGenerated K sigma) :
    ∃u∈signedFixed K sigma false,∃d∈pairNormalizer K sigma,∃i:Menu,
      ∃v∈signedFixed K sigma false,g=u*d*menuMatrix K i*v := by
  have hgM := fixedRootGenerated_le_matrixGroup K sigma hg
  have hfix : unitTwist K sigma g=g := fixedRootGenerated_le_fixed K sigma hg
  obtain ⟨r,b,hb,v,he⟩ := exists_relative_inversion_cell K sigma g hgM hfix
  let W := wordUnit (CartanMatrix.D 4) (CartanMatrix.D_transpose 4) D4_positive_definite
    Base Index K (expandRelative r)
  let V := inversionEmbedding K (expandRelative r) v
  change g=b*W*V at he
  have hW : unitTwist K sigma W=W := by
    simpa only [W,word_eq_canonicalWord] using relative_word_fixed K sigma r
  have ht : unitTwist K sigma (b*W*V)=(1:MatrixGroup K).val*(b*W*V) := by
    change unitTwist K sigma (b*W*V)=1*(b*W*V)
    rw [one_mul,←he]
    exact hfix
  have hc := central_twisted_cell_coordinates K sigma (expandRelative r) hW
    (1:MatrixGroup K) (Subgroup.one_mem _) ⟨b,hb⟩ v ht
  obtain ⟨u,hu,huf,d,hd,hdf,hbprod⟩ := exists_central_twisted_envelope_factors
    K sigma b hb (1:MatrixGroup K) (Subgroup.one_mem _) hc.1
  have huF : u∈signedFixed K sigma false := ⟨hu,huf⟩
  have hvF : V∈signedFixed K sigma false := ⟨v.val.property,hc.2⟩
  have huJ := signedFixed_le_generated K sigma false huF
  have hvJ := signedFixed_le_generated K sigma false hvF
  have hWJ : W∈fixedRootGenerated K sigma := relativeWord_mem_generated K sigma r
  have hprod : g=u*d*W*V := he.trans (congrArg (fun x=>x*W*V) hbprod)
  have hdJ : d∈fixedRootGenerated K sigma := by
    have hh := (fixedRootGenerated K sigma).mul_mem
      ((fixedRootGenerated K sigma).mul_mem ((fixedRootGenerated K sigma).inv_mem huJ) hg)
      ((fixedRootGenerated K sigma).inv_mem ((fixedRootGenerated K sigma).mul_mem hWJ hvJ))
    have heD : u⁻¹*g*(W*V)⁻¹=d := by rw [hprod];group
    exact heD ▸ hh
  have hdPair := fixed_diagonal_mem_pair K sigma d hd hdJ
  obtain ⟨i,e,heD,heW⟩ := exists_menu_matrix_factor K (expandRelative r)
    (relative_root_action_commutes r)
  have heJ : e∈fixedRootGenerated K sigma := by
    have hh := (fixedRootGenerated K sigma).mul_mem hWJ
      ((fixedRootGenerated K sigma).inv_mem (menuMatrix_mem_generated K sigma i))
    have hee : W*(menuMatrix K i)⁻¹=e := by
      change W=e*menuMatrix K i at heW
      rw [heW]
      group
    exact hee ▸ hh
  have hePair := fixed_diagonal_mem_pair K sigma e heD heJ
  refine ⟨u,huF,d*e,(pairNormalizer K sigma).mul_mem hdPair hePair,i,V,hvF,?_⟩
  change W=e*menuMatrix K i at heW
  rw [hprod,heW]
  group

end SymmetricSubgroupAsymptotics.CFSGTrialityGeckFiniteFixedBruhatCover
