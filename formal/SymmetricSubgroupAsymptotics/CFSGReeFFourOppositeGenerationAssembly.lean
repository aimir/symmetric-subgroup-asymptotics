import SymmetricSubgroupAsymptotics.CFSGReeFFourOuterUnipotentGeneration

/-! The actual fixed Bruhat cover reduces opposite-unipotent generation
to the middle Weyl word and the middle torus words. The outer words are
already proved members. The two middle membership hypotheses below are
explicit remaining group-theory obligations, not classification inputs. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics.CFSGReeFFourOppositeGenerationAssembly
open CFSGReeFFourFieldParameters CFSGReeFFourFixedModelEquivalence
open CFSGReeFFourFixedTorus CFSGReeFFourFixedDiagonalTorus CFSGReeFFourFixedBruhatCover
open CFSGReeFFourRelativeSimpleWeyl CFSGReeFFourOriginalWeylWords
open CFSGReeFFourPairedModelWords CFSGReeFFourPairedWordActions
open CFSGReeFFourFixedWordClassification CFSGFFourOriginalProductTorus
open CFSGReeFFourParameterizedTorusCovariance CFSGReeFFourOuterUnipotentGeneration

def fixedMiddleWeyl (m : ℕ) : originalModelFixed m :=
  ⟨middleRelativeWeyl m, middleRelativeWeyl_fixed m⟩

theorem fixedTorus_split (m : ℕ) (a b : (Field m)ˣ) :
    fixedTorus m a b = fixedTorus m a 1 * fixedTorus m 1 b := by
  have hu (i : Fin 4) : unitPower m i 1 = 1 := by
    apply Units.ext
    simp only [unitPower_val, Units.val_one, one_pow]
  have ht : fixedTorusTuple m a b = fixedTorusTuple m a 1 * fixedTorusTuple m 1 b := by
    funext i
    fin_cases i <;> simp [fixedTorusTuple, hu]
  apply Subtype.ext
  change modelProductTorusHom (Field m) (fixedTorusTuple m a b) =
    modelProductTorusHom (Field m) (fixedTorusTuple m a 1) *
      modelProductTorusHom (Field m) (fixedTorusTuple m 1 b)
  rw [ht, map_mul]

theorem fixedPairedWord_mem_of_middle (m : ℕ)
    (hW : fixedMiddleWeyl m ∈ oppositeGenerated m) (s : List Bool) :
    fixedPairedWord m s ∈ oppositeGenerated m := by
  induction s with
  | nil => exact (oppositeGenerated m).one_mem
  | cons b s ih =>
      cases b
      · have he : fixedPairedWord m (false :: s) =
            fixedOuterWeyl m 1 * fixedPairedWord m s := by
          apply Subtype.ext
          change modelWeylWord (Field m) (pairedRelativeWord false ++ expandPaired s) =
            (fixedOuterWeyl m 1).val * modelWeylWord (Field m) (expandPaired s)
          rw [modelWeylWord_append, fixedOuterWeyl_one_val]
          simp only [pairedRelativeWord, Bool.false_eq_true, if_false,
            modelWeylWord, mul_one, outerRelativeWeyl]
        rw [he]
        exact (oppositeGenerated m).mul_mem (fixedOuterWeyl_mem m 1) ih
      · have he : fixedPairedWord m (true :: s) =
            fixedMiddleWeyl m * fixedPairedWord m s := by
          apply Subtype.ext
          change modelWeylWord (Field m) (pairedRelativeWord true ++ expandPaired s) =
            middleRelativeWeyl m * modelWeylWord (Field m) (expandPaired s)
          rw [modelWeylWord_append]
          simp only [pairedRelativeWord, if_true, modelWeylWord, mul_one,
            middleRelativeWeyl, mul_assoc]
        rw [he]
        exact (oppositeGenerated m).mul_mem hW ih

theorem oppositeGenerated_eq_top_of_middle (m : ℕ)
    (hW : fixedMiddleWeyl m ∈ oppositeGenerated m)
    (hT : ∀ b : (Field m)ˣ, fixedTorus m 1 b ∈ oppositeGenerated m) :
    oppositeGenerated m = ⊤ := by
  apply top_unique
  intro g _
  obtain ⟨u, hu, d, hd, s, v, hv, hg⟩ := exists_fixed_four_factor_cell m g
  obtain ⟨a, b, rfl⟩ := exists_fixedDiagonal_torus m d hd
  have htorus : fixedTorus m a b ∈ oppositeGenerated m := by
    rw [fixedTorus_split]
    exact (oppositeGenerated m).mul_mem (fixedTorus_outer_mem m a) (hT b)
  rw [hg]
  exact (oppositeGenerated m).mul_mem
    ((oppositeGenerated m).mul_mem
      ((oppositeGenerated m).mul_mem (positive_le m hu) htorus)
      (fixedPairedWord_mem_of_middle m hW s)) (positive_le m hv)

end SymmetricSubgroupAsymptotics.CFSGReeFFourOppositeGenerationAssembly
