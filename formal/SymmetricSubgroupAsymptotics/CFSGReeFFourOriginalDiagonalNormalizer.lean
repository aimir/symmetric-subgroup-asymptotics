import SymmetricSubgroupAsymptotics.CFSGReeFFourFixedDiagonalNormalizer
import SymmetricSubgroupAsymptotics.CFSGReeFFourOriginalPairDiagonal
import SymmetricSubgroupAsymptotics.CFSGReeFFourShortPairedWeylMenu

/-! Elementwise diagonal-normalizer descent to the SAME original Ree
quotient. Only elements are lifted through the proved surjection;
no automorphism of the quotient is lifted. Equal word actions retain
the actual diagonal residual. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGReeFFourOriginalDiagonalNormalizer
open CFSGReeFFourFixedModelEquivalence CFSGReeFFourPerfectProjection
open CFSGReeFFourFixedBruhatCover CFSGReeFFourOriginalPairDiagonal
open CFSGReeFFourOriginalBorelNormalizers CFSGReeFFourFixedDiagonalNormalizer
open CFSGReeFFourPairedWordDiagonalNormalization CFSGReeFFourOriginalPairRestriction
open CFSGReeFFourShortPairedWeylMenu CFSGReeFFourPairedModelWords
open CFSGReeFFourFieldParameters CFSGReeFFourFixedWordClassification

def originalPairedWord (m : ℕ) (hm : 0<m) (w : List Bool) : CFSG.Models.ReeF4 m :=
  fixedToOriginal m hm (fixedPairedWord m w)

theorem originalDiagonal_comap (m : ℕ) (hm : 0<m) :
    (originalDiagonal m hm).comap (fixedToOriginal m hm)=fixedDiagonal m := by
  rw [←fixedDiagonal_map_originalDiagonal]
  exact Subgroup.comap_map_eq_self (fixedToOriginal_kernel_le_diagonal m hm)

theorem originalPairedWord_normalizes_diagonal (m : ℕ) (hm : 0<m) (w : List Bool) :
    originalPairedWord m hm w∈Subgroup.normalizer
      (originalDiagonal m hm : Set (CFSG.Models.ReeF4 m)) := by
  rw [←fixedDiagonal_map_originalDiagonal]
  exact Subgroup.le_normalizer_map (fixedToOriginal m hm)
    ⟨fixedPairedWord m w,fixedPairedWord_normalizes_diagonal m w,rfl⟩

theorem exists_diagonal_paired_word_of_normalizes_original_diagonal
    (m : ℕ) (hm : 0<m) (x : CFSG.Models.ReeF4 m)
    (hx : x∈Subgroup.normalizer (originalDiagonal m hm : Set (CFSG.Models.ReeF4 m))) :
    ∃ (w : List Bool) (d : originalDiagonal m hm),x=d.val*originalPairedWord m hm w := by
  obtain ⟨g,rfl⟩ := fixedToOriginal_surjective m hm x
  have hg : g∈Subgroup.normalizer (fixedDiagonal m : Set (originalModelFixed m)) := by
    have h := Subgroup.le_normalizer_comap (fixedToOriginal m hm) hx
    rwa [originalDiagonal_comap] at h
  obtain ⟨w,d,hd,he⟩ := exists_diagonal_paired_word_of_normalizes_diagonal m hm g hg
  refine ⟨w,⟨fixedToOriginal m hm d,?_⟩,?_⟩
  · rw [←fixedDiagonal_map_originalDiagonal]
    exact ⟨d,hd,rfl⟩
  · exact (congrArg (fixedToOriginal m hm) he).trans (map_mul _ _ _)

private theorem map_residual_factor {G H : Type*} [Group G] [Group H]
    (f : G→*H) (a b : G) : f a=f (a*b⁻¹)*f b := by
  rw [map_mul,map_inv]
  group

theorem exists_diagonal_short_word_of_normalizes_original_diagonal
    (m : ℕ) (hm : 0<m) (x : CFSG.Models.ReeF4 m)
    (hx : x∈Subgroup.normalizer (originalDiagonal m hm : Set (CFSG.Models.ReeF4 m))) :
    ∃ (i : Fin 16) (d : originalDiagonal m hm),
      x=d.val*originalPairedWord m hm (shortWord i) := by
  obtain ⟨w,d,he⟩ := exists_diagonal_paired_word_of_normalizes_original_diagonal m hm x hx
  obtain ⟨i,hi⟩ := exists_short_menu_action w
  let delta : originalModelFixed m := fixedPairedWord m w*(fixedPairedWord m (shortWord i))⁻¹
  have hdelta : delta∈fixedDiagonal m :=
    equal_action_model_residual_mem (Field m) (expandPaired w) (expandPaired (shortWord i)) hi
  have hdeltapi : fixedToOriginal m hm delta∈originalDiagonal m hm := by
    rw [←fixedDiagonal_map_originalDiagonal]
    exact ⟨delta,hdelta,rfl⟩
  refine ⟨i,⟨d.val*fixedToOriginal m hm delta,(originalDiagonal m hm).mul_mem d.property hdeltapi⟩,
    he.trans ?_⟩
  have hword : originalPairedWord m hm w=
      fixedToOriginal m hm delta*originalPairedWord m hm (shortWord i) := by
    exact map_residual_factor (fixedToOriginal m hm)
      (fixedPairedWord m w) (fixedPairedWord m (shortWord i))
  rw [hword,mul_assoc]

theorem pair_image_originalPairedWord_normalizes_diagonal (m : ℕ) (hm : 0<m)
    (f : pairStabilizer m hm) (w : List Bool) :
    f.val (originalPairedWord m hm w)∈Subgroup.normalizer
      (originalDiagonal m hm : Set (CFSG.Models.ReeF4 m)) := by
  have hmap : (Subgroup.normalizer (originalDiagonal m hm : Set (CFSG.Models.ReeF4 m))).map
      f.val.toMonoidHom=Subgroup.normalizer (originalDiagonal m hm : Set (CFSG.Models.ReeF4 m)) :=
    (Subgroup.map_equiv_normalizer_eq (originalDiagonal m hm) f.val).trans
    (congrArg (fun P : Subgroup (CFSG.Models.ReeF4 m)=>Subgroup.normalizer
      (P : Set (CFSG.Models.ReeF4 m))) (originalDiagonal_map_pair m hm f))
  rw [←hmap]
  exact ⟨originalPairedWord m hm w,originalPairedWord_normalizes_diagonal m hm w,rfl⟩

end SymmetricSubgroupAsymptotics.CFSGReeFFourOriginalDiagonalNormalizer
