import SymmetricSubgroupAsymptotics.CFSGReeFFourSimpleBlockPeelingGeneration
import SymmetricSubgroupAsymptotics.CFSGReeFFourMiddleWeylConstantWord
import SymmetricSubgroupAsymptotics.CFSGReeFFourMiddleNegativeFamily
import SymmetricSubgroupAsymptotics.CFSGReeFFourOuterUnipotentGeneration

/-! The actual two relative Weyl words lie in any subgroup containing
the four signed simple blocks. The middle proof uses its checked constant
word with a genuinely negative middle factor. No rank-one recognition
or equality of source words from lattice actions is used. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics.CFSGReeFFourSignedBlockWeylGeneration
open CFSGReeFFourFieldParameters CFSGReeFFourFixedModelEquivalence
open CFSGReeFFourFixedPositiveFamilies CFSGReeFFourFixedBruhatCover
open CFSGReeFFourFixedBorelCardinality CFSGReeFFourMinimalParabolics
open CFSGReeFFourOppositionFixedPositiveNegative CFSGReeFFourSimpleBlockPeelingGeneration
open CFSGReeFFourOuterUnipotentGeneration CFSGReeFFourOuterFixedRoot
open CFSGReeFFourMiddleFixedWords CFSGReeFFourMiddleFixedSubgroup
open CFSGReeFFourMiddleNegativeFamily CFSGReeFFourMiddleWeylConstantWord
open CFSGReeFFourOppositeGenerationAssembly CFSGReeFFourSimpleInversionBlocks
open CFSGFFourOriginalMiddleWords CFSGFFourE6FixedGeneratedGroup CFSGSerreQuadraticMatrix
open CFSGTwistedE6GeckDiagramCovariance CFSGNormTwoGeckPositivePGroup
open CFSGExceptionalNormTwoBases CFSGExceptionalCartanPositiveDefinite
open CFSGOpposedSubgroupPeeling
local notation "R" => CFSGTwistedE6GeckDiagramCovariance.rawData

theorem fixedSignedOuter_negative_mem (m : ℕ) (a : Field m) :
    fixedSignedOuter m true a∈fixedNegative m := by
  change rawHom (Field m) (signedOuterWord m true a)∈
    rootGroup CartanMatrix.E₆ CartanMatrix.E₆_transpose E6_positive_definite
      E6Base E6Index (Field m) true
  simp only [signedOuterWord,map_mul,rawHom_root,folded_root_eq_orbitParameter]
  change (canonicalRoot R (Field m) true 0 a*canonicalRoot R (Field m) true 5 a)*
    canonicalRoot R (Field m) true 1 (alpha m a)∈
      rootGroup CartanMatrix.E₆ CartanMatrix.E₆_transpose E6_positive_definite
        E6Base E6Index (Field m) true
  exact Subgroup.mul_mem _
    (Subgroup.mul_mem _ (Subgroup.subset_closure ⟨(0,a),rfl⟩)
      (Subgroup.subset_closure ⟨(5,a),rfl⟩))
    (Subgroup.subset_closure ⟨(1,alpha m a),rfl⟩)

private theorem simpleWeyl_mem_parabolic (m : ℕ) (b : Bool) :
    simpleWeyl m b∈simpleParabolic m b :=
  (show Subgroup.closure {simpleWeyl m b}≤simpleParabolic m b from le_sup_right)
    (Subgroup.subset_closure (Set.mem_singleton _))

private theorem positive_le_parabolic (m : ℕ) (b : Bool) : fixedPositive m≤simpleParabolic m b :=
  (positive_le_borel m).trans le_sup_left

private theorem middle_parameter_mem (m : ℕ) (p : Field m×Field m) :
    fixedMiddleParameter m p∈inversionPart (fixedPositive m) (fixedNegative m) (simpleWeyl m true) := by
  rw [middle_simple_inversion_eq]
  exact ⟨p.1,alpha m p.1,p.2,alpha m p.2+p.1^2*alpha m p.1,rfl⟩

theorem simpleWeyl_mem_of_signed_blocks (m : ℕ) (S : Subgroup (originalModelFixed m))
    (hpos : ∀b : Bool,inversionPart (fixedPositive m) (fixedNegative m) (simpleWeyl m b)≤S)
    (hneg : ∀b : Bool,fixedNegative m⊓simpleParabolic m b≤S) (b : Bool) :
    simpleWeyl m b∈S := by
  cases b
  · let p := fixedSignedOuter m false 1
    let n := fixedSignedOuter m true (-1)
    have hp : p∈inversionPart (fixedPositive m) (fixedNegative m) (simpleWeyl m false) := by
      rw [outer_simple_inversion_eq]
      exact ⟨Multiplicative.ofAdd 1,rfl⟩
    have hpP := positive_le_parabolic m false hp.1
    have hW : simpleWeyl m false=fixedOuterWeyl m 1 := by
      apply Subtype.ext
      exact (single_paired_word_val m false).trans (fixedOuterWeyl_one_val m).symm
    have he : simpleWeyl m false=p*n*p := by
      rw [hW]
      simp only [fixedOuterWeyl,Units.val_one,inv_one]
      rfl
    have hnP : n∈simpleParabolic m false := by
      have hh := (simpleParabolic m false).mul_mem
        ((simpleParabolic m false).mul_mem ((simpleParabolic m false).inv_mem hpP)
          (simpleWeyl_mem_parabolic m false)) ((simpleParabolic m false).inv_mem hpP)
      have hhval : p⁻¹*simpleWeyl m false*p⁻¹=n := by rw [he];group
      exact hhval ▸ hh
    have hn : n∈S := hneg false ⟨fixedSignedOuter_negative_mem m (-1),hnP⟩
    rw [he]
    exact S.mul_mem (S.mul_mem (hpos false hp) hn) (hpos false hp)
  · let W := fixedMiddleWeyl m
    let z := W*fixedMiddleParameter m (1,0)*W⁻¹
    have hp (p : Field m×Field m) : fixedMiddleParameter m p∈S := hpos true (middle_parameter_mem m p)
    have hWP : W∈simpleParabolic m true := by
      have hh := simpleWeyl_mem_parabolic m true
      rw [simpleWeyl_true] at hh
      exact hh
    have hpP : fixedMiddleParameter m (1,0)∈simpleParabolic m true :=
      positive_le_parabolic m true (middle_parameter_mem m (1,0)).1
    have hzP : z∈simpleParabolic m true :=
      (simpleParabolic m true).mul_mem ((simpleParabolic m true).mul_mem hWP hpP)
        ((simpleParabolic m true).inv_mem hWP)
    have hzV : z∈fixedNegative m := by
      apply middle_conjugate_middleFixedSubgroup_le m
      refine ⟨fixedMiddleParameter m (1,0),?_,rfl⟩
      rw [←middle_simple_inversion_eq]
      exact middle_parameter_mem m (1,0)
    have hz : z∈S := hneg true ⟨hzV,hzP⟩
    have he : W=fixedMiddleParameter m (0,1)*z*fixedMiddleParameter m (1,1) := by
      apply Subtype.ext
      exact middleRelativeWeyl_constant_factors m
    have hWS : W∈S := by
      rw [he]
      exact S.mul_mem (S.mul_mem (hp (0,1)) hz) (hp (1,1))
    rw [simpleWeyl_true]
    exact hWS

end SymmetricSubgroupAsymptotics.CFSGReeFFourSignedBlockWeylGeneration
