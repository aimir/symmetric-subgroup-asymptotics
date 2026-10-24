import SymmetricSubgroupAsymptotics.CFSGReeFFourOriginalDiagonalNormalizer
import SymmetricSubgroupAsymptotics.CFSGReeFFourOriginalParabolicLabels
import SymmetricSubgroupAsymptotics.CFSGReeFFourMiddleParabolicWordMenu
import SymmetricSubgroupAsymptotics.CFSGReeFFourOriginalNegativeMiddleCoordinates
import SymmetricSubgroupAsymptotics.CFSGReeFFourOriginalOuterWeylCoset

/-! The actual middle reflection coset is intrinsic in the original
Ree quotient. The parabolic flag reduces the finite word menu to two
actions; diagonal invariance excludes the identity coset. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGReeFFourOriginalMiddleWeylCoset
open CFSGReeFFourOriginalDiagonalNormalizer CFSGReeFFourOriginalParabolicLabels
open CFSGReeFFourOriginalNegativeMiddleCoordinates CFSGReeFFourOriginalOuterWeylCoset
open CFSGReeFFourMiddleParabolicWordMenu CFSGReeFFourShortPairedWeylMenu
open CFSGReeFFourOriginalMinimalParabolics CFSGReeFFourMinimalParabolics
open CFSGReeFFourOriginalPairRestriction CFSGReeFFourOriginalPairDiagonal
open CFSGReeFFourPerfectProjection CFSGReeFFourOriginalBorelNormalizers
open CFSGReeFFourFixedBruhatCover CFSGReeFFourFixedModelEquivalence
open CFSGReeFFourFixedBorelCardinality CFSGReeFFourMiddleParabolicFlag
open CFSGReeFFourOriginalWeylWords CFSGReeFFourFieldParameters
open CFSGReeFFourFixedWordClassification CFSGReeFFourFixedPositiveFamilies
open CFSGFFourOriginalMiddleWords CFSGReeFFourRelativePositiveSubgroups

theorem originalMiddleWeyl_eq_pairedWord (m : ℕ) (hm : 0<m) :
    originalMiddleWeyl m hm=originalPairedWord m hm [true] := by
  change fixedToOriginal m hm (middleFixedWeyl m)=fixedToOriginal m hm (simpleWeyl m true)
  exact congrArg (fixedToOriginal m hm) (simpleWeyl_true m).symm

private theorem diagonal_le_originalSimpleParabolic (m : ℕ) (hm : 0<m) (b : Bool) :
    originalDiagonal m hm≤originalSimpleParabolic m hm b := by
  rw [←fixedDiagonal_map_originalDiagonal]
  exact Subgroup.map_mono ((diagonal_le_borel m).trans le_sup_left)

private theorem short_word_parabolic_only (m : ℕ) (hm : 0<m) (i : Fin 16)
    (hi : originalPairedWord m hm (shortWord i)∈originalSimpleParabolic m hm true) :
    i=0∨i=2 := by
  have hsource : fixedPairedWord m (shortWord i)∈simpleParabolic m true := by
    have hh : fixedPairedWord m (shortWord i)∈
        (originalSimpleParabolic m hm true).comap (fixedToOriginal m hm) := hi
    rwa [originalSimpleParabolic_comap] at hh
  rw [simpleParabolic_true] at hsource
  have hflag := middleParabolic_le_flag m hsource
  change rawHom (Field m)
    (modelWeylWord (Field m) (expandPaired (shortWord i)))∈middleFlag (Field m) at hflag
  rw [rawHom_modelWeylWord_relative] at hflag
  exact short_word_mem_middleFlag_only (Field m) i hflag

theorem originalMiddleWeyl_not_mem_diagonal (m : ℕ) (hm : 0<m) :
    originalMiddleWeyl m hm∉originalDiagonal m hm := by
  intro hD
  have hsource : fixedPairedWord m [true]∈fixedDiagonal m := by
    have hh : fixedPairedWord m [true]∈(originalDiagonal m hm).comap (fixedToOriginal m hm) := by
      change originalPairedWord m hm [true]∈originalDiagonal m hm
      rwa [←originalMiddleWeyl_eq_pairedWord]
    rwa [originalDiagonal_comap] at hh
  exact other_simple_not_mem_parabolic m false true (by decide)
    (((diagonal_le_borel m).trans (show fixedBorel m≤simpleParabolic m false from le_sup_left)) hsource)

theorem exists_diagonal_middle_of_normalizes_diagonal_mem_middleParabolic
    (m : ℕ) (hm : 0<m) (x : CFSG.Models.ReeF4 m)
    (hN : x∈Subgroup.normalizer (originalDiagonal m hm : Set (CFSG.Models.ReeF4 m)))
    (hP : x∈originalSimpleParabolic m hm true) (hD : x∉originalDiagonal m hm) :
    ∃d : originalDiagonal m hm,x=d.val*originalMiddleWeyl m hm := by
  obtain ⟨i,d,he⟩ := exists_diagonal_short_word_of_normalizes_original_diagonal m hm x hN
  have hshort : originalPairedWord m hm (shortWord i)∈originalSimpleParabolic m hm true := by
    have hh := (originalSimpleParabolic m hm true).mul_mem
      ((originalSimpleParabolic m hm true).inv_mem
        (diagonal_le_originalSimpleParabolic m hm true d.property)) hP
    have hc : d.val⁻¹*x=originalPairedWord m hm (shortWord i) := by rw [he];group
    rwa [hc] at hh
  rcases short_word_parabolic_only m hm i hshort with h0|h1
  · subst i
    have hz : originalPairedWord m hm (shortWord (0 : Fin 16))=1 := by
      change fixedToOriginal m hm 1=1
      exact map_one _
    exact False.elim (hD (by rw [he,hz,mul_one];exact d.property))
  · subst i
    change x=d.val*originalPairedWord m hm [true] at he
    exact ⟨d,he.trans (congrArg (fun z=>d.val*z) (originalMiddleWeyl_eq_pairedWord m hm).symm)⟩

theorem pair_image_middleWeyl_mem_diagonal_coset (m : ℕ) (hm : 0<m)
    (f : pairStabilizer m hm) :
    ∃d : originalDiagonal m hm,f.val (originalMiddleWeyl m hm)=d.val*originalMiddleWeyl m hm := by
  have hN : f.val (originalMiddleWeyl m hm)∈Subgroup.normalizer
      (originalDiagonal m hm : Set (CFSG.Models.ReeF4 m)) := by
    rw [originalMiddleWeyl_eq_pairedWord]
    exact pair_image_originalPairedWord_normalizes_diagonal m hm f [true]
  have hW : originalMiddleWeyl m hm∈originalSimpleParabolic m hm true := by
    apply Subgroup.mem_map.mpr
    refine ⟨simpleWeyl m true,?_,?_⟩
    · exact (show Subgroup.closure {simpleWeyl m true}≤simpleParabolic m true from le_sup_right)
        (Subgroup.subset_closure (Set.mem_singleton _))
    · change originalPairedWord m hm [true]=originalMiddleWeyl m hm
      exact (originalMiddleWeyl_eq_pairedWord m hm).symm
  have hP : f.val (originalMiddleWeyl m hm)∈originalSimpleParabolic m hm true := by
    rw [←original_simple_parabolic_map_eq m hm f.val
      (pair_preserves_positive m hm f) (pair_preserves_negative m hm f) true]
    exact ⟨originalMiddleWeyl m hm,hW,rfl⟩
  have hD : f.val (originalMiddleWeyl m hm)∉originalDiagonal m hm := by
    intro hd
    have hmap : f.val (originalMiddleWeyl m hm)∈(originalDiagonal m hm).map f.val.toMonoidHom := by
      rw [originalDiagonal_map_pair]
      exact hd
    obtain ⟨y,hy,he⟩ := hmap
    have heq : y=originalMiddleWeyl m hm := f.val.injective he
    exact originalMiddleWeyl_not_mem_diagonal m hm (heq ▸hy)
  exact exists_diagonal_middle_of_normalizes_diagonal_mem_middleParabolic m hm _ hN hP hD

end SymmetricSubgroupAsymptotics.CFSGReeFFourOriginalMiddleWeylCoset
