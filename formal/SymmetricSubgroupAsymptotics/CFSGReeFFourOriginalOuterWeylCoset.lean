import SymmetricSubgroupAsymptotics.CFSGReeFFourOriginalDiagonalNormalizer
import SymmetricSubgroupAsymptotics.CFSGReeFFourOriginalParabolicLabels
import SymmetricSubgroupAsymptotics.CFSGReeFFourOuterParabolicWordMenu

/-! The actual outer reflection coset is intrinsic in the original
Ree quotient. The parabolic flag reduces the finite word menu to two
actions; diagonal invariance excludes the identity coset. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGReeFFourOriginalOuterWeylCoset
open CFSGReeFFourOriginalDiagonalNormalizer CFSGReeFFourOriginalParabolicLabels
open CFSGReeFFourOuterParabolicWordMenu CFSGReeFFourShortPairedWeylMenu
open CFSGReeFFourOriginalMinimalParabolics CFSGReeFFourMinimalParabolics
open CFSGReeFFourOriginalPairRestriction CFSGReeFFourOriginalPairDiagonal
open CFSGReeFFourPerfectProjection CFSGReeFFourOriginalBorelNormalizers
open CFSGReeFFourFixedBruhatCover CFSGReeFFourFixedModelEquivalence
open CFSGReeFFourFixedBorelCardinality CFSGReeFFourOuterParabolicFlag
open CFSGReeFFourOriginalWeylWords CFSGReeFFourFieldParameters
open CFSGReeFFourFixedWordClassification CFSGReeFFourFixedPositiveFamilies
open CFSGFFourOriginalMiddleWords CFSGReeFFourRelativePositiveSubgroups

def originalOuterWeyl (m : ℕ) (hm : 0<m) : CFSG.Models.ReeF4 m :=
  originalPairedWord m hm [false]

theorem originalSimpleParabolic_comap (m : ℕ) (hm : 0<m) (b : Bool) :
    (originalSimpleParabolic m hm b).comap (fixedToOriginal m hm)=simpleParabolic m b :=
  Subgroup.comap_map_eq_self ((fixedToOriginal_kernel_le_borel m hm).trans le_sup_left)

private theorem diagonal_le_originalSimpleParabolic (m : ℕ) (hm : 0<m) (b : Bool) :
    originalDiagonal m hm≤originalSimpleParabolic m hm b := by
  rw [←fixedDiagonal_map_originalDiagonal]
  exact Subgroup.map_mono ((diagonal_le_borel m).trans le_sup_left)

private theorem short_word_parabolic_only (m : ℕ) (hm : 0<m) (i : Fin 16)
    (hi : originalPairedWord m hm (shortWord i)∈originalSimpleParabolic m hm false) :
    i=0∨i=1 := by
  have hsource : fixedPairedWord m (shortWord i)∈simpleParabolic m false := by
    have hh : fixedPairedWord m (shortWord i)∈
        (originalSimpleParabolic m hm false).comap (fixedToOriginal m hm) := hi
    rwa [originalSimpleParabolic_comap] at hh
  rw [simpleParabolic_false] at hsource
  have hflag := outerParabolic_le_flag m hsource
  change rawHom (Field m)
    (modelWeylWord (Field m) (expandPaired (shortWord i)))∈outerFlag (Field m) at hflag
  rw [rawHom_modelWeylWord_relative] at hflag
  exact short_word_mem_outerFlag_only (Field m) i hflag

theorem originalOuterWeyl_not_mem_diagonal (m : ℕ) (hm : 0<m) :
    originalOuterWeyl m hm∉originalDiagonal m hm := by
  intro hD
  have hsource : fixedPairedWord m [false]∈fixedDiagonal m := by
    have hh : fixedPairedWord m [false]∈(originalDiagonal m hm).comap (fixedToOriginal m hm) := hD
    rwa [originalDiagonal_comap] at hh
  exact other_simple_not_mem_parabolic m true false (by decide)
    (((diagonal_le_borel m).trans (show fixedBorel m≤simpleParabolic m true from le_sup_left)) hsource)

theorem exists_diagonal_outer_of_normalizes_diagonal_mem_outerParabolic
    (m : ℕ) (hm : 0<m) (x : CFSG.Models.ReeF4 m)
    (hN : x∈Subgroup.normalizer (originalDiagonal m hm : Set (CFSG.Models.ReeF4 m)))
    (hP : x∈originalSimpleParabolic m hm false) (hD : x∉originalDiagonal m hm) :
    ∃d : originalDiagonal m hm,x=d.val*originalOuterWeyl m hm := by
  obtain ⟨i,d,he⟩ := exists_diagonal_short_word_of_normalizes_original_diagonal m hm x hN
  have hshort : originalPairedWord m hm (shortWord i)∈originalSimpleParabolic m hm false := by
    have hh := (originalSimpleParabolic m hm false).mul_mem
      ((originalSimpleParabolic m hm false).inv_mem
        (diagonal_le_originalSimpleParabolic m hm false d.property)) hP
    have hc : d.val⁻¹*x=originalPairedWord m hm (shortWord i) := by rw [he];group
    rwa [hc] at hh
  rcases short_word_parabolic_only m hm i hshort with h0|h1
  · subst i
    have hz : originalPairedWord m hm (shortWord (0 : Fin 16))=1 := by
      change fixedToOriginal m hm 1=1
      exact map_one _
    exact False.elim (hD (by rw [he,hz,mul_one];exact d.property))
  · subst i
    exact ⟨d,he⟩

theorem pair_image_outerWeyl_mem_diagonal_coset (m : ℕ) (hm : 0<m)
    (f : pairStabilizer m hm) :
    ∃d : originalDiagonal m hm,f.val (originalOuterWeyl m hm)=d.val*originalOuterWeyl m hm := by
  have hN := pair_image_originalPairedWord_normalizes_diagonal m hm f [false]
  have hW : originalOuterWeyl m hm∈originalSimpleParabolic m hm false := by
    apply Subgroup.mem_map.mpr
    refine ⟨simpleWeyl m false,?_,rfl⟩
    exact (show Subgroup.closure {simpleWeyl m false}≤simpleParabolic m false from le_sup_right)
      (Subgroup.subset_closure (Set.mem_singleton _))
  have hP : f.val (originalOuterWeyl m hm)∈originalSimpleParabolic m hm false := by
    rw [←original_simple_parabolic_map_eq m hm f.val
      (pair_preserves_positive m hm f) (pair_preserves_negative m hm f) false]
    exact ⟨originalOuterWeyl m hm,hW,rfl⟩
  have hD : f.val (originalOuterWeyl m hm)∉originalDiagonal m hm := by
    intro hd
    have hmap : f.val (originalOuterWeyl m hm)∈(originalDiagonal m hm).map f.val.toMonoidHom := by
      rw [originalDiagonal_map_pair]
      exact hd
    obtain ⟨y,hy,he⟩ := hmap
    have heq : y=originalOuterWeyl m hm := f.val.injective he
    exact originalOuterWeyl_not_mem_diagonal m hm (heq ▸hy)
  exact exists_diagonal_outer_of_normalizes_diagonal_mem_outerParabolic m hm _ hN hP hD

end SymmetricSubgroupAsymptotics.CFSGReeFFourOriginalOuterWeylCoset
