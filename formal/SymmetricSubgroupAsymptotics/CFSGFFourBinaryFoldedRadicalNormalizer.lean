import SymmetricSubgroupAsymptotics.CFSGFFourBinaryLeviWeylNormalizer

/-! The literal binary radical and its checked normalizers inside the
actual folded F4 matrix group. The fixed-positive inclusion supplies the
source membership; all covariance remains the existing matrix covariance.
No independent recognition or new simple-group assumption is used. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGFFourBinaryFoldedRadicalNormalizer
open CFSGFFourBinaryFixedRadicalEmbedding CFSGFFourE6FixedPositiveProjection
open CFSGFFourBinaryPositiveLeviNormalizer CFSGFFourBinaryLeviWeylNormalizer
open CFSGFFourSerreMatrices CFSGSerreQuadraticMatrix CFSGSerreQuadraticWeylWord
local instance fFourFoldedRadicalRootsDecidableEq :
    DecidableEq (CFSGNormTwoRootPairing.Roots CartanMatrix.E₆) := Classical.decEq _
variable (K : Type) [Field K] [Finite K] [CharP K 2]
private abbrev Folded := canonicalElementaryGroup realizationData K

def foldedHom : Radical K →* Folded K :=
  (fixedPositiveToFolded K).comp (fixedPositiveHom K)

theorem foldedHom_val (v : Radical K) : (foldedHom K v).val = matrixHom K v := rfl

theorem foldedHom_injective : Function.Injective (foldedHom K) := by
  intro v w h
  exact matrixHom_injective K (congrArg Subtype.val h)

theorem foldedHom_range_eq_comap :
    (foldedHom K).range = (matrixHom K).range.comap (Folded K).subtype := by
  ext g
  constructor
  · rintro ⟨v,rfl⟩
    exact ⟨v,rfl⟩
  · intro hg
    change g.val ∈ (matrixHom K).range at hg
    obtain ⟨v,hv⟩ := hg
    exact ⟨v,Subtype.ext hv⟩

theorem positive_mem_normalizer (n : Fin 3) (a : K) :
    canonicalElementaryRoot realizationData K false n.castSucc a ∈
      Subgroup.normalizer ((foldedHom K).range : Set (Folded K)) := by
  rw [foldedHom_range_eq_comap]
  exact (Subgroup.le_normalizer_comap (H := (matrixHom K).range) (Folded K).subtype)
    (folded_positive_mem_radical_normalizer K n a)

def foldedWeyl (n : Fin 3) : Folded K :=
  canonicalElementaryRoot realizationData K false n.castSucc 1 *
    canonicalElementaryRoot realizationData K true n.castSucc (-1) *
    canonicalElementaryRoot realizationData K false n.castSucc 1

omit [Finite K] [CharP K 2] in
theorem foldedWeyl_val (n : Fin 3) :
    (foldedWeyl K n).val = canonicalWeyl realizationData K n.castSucc := rfl

theorem weyl_mem_normalizer (n : Fin 3) : foldedWeyl K n ∈
    Subgroup.normalizer ((foldedHom K).range : Set (Folded K)) := by
  rw [foldedHom_range_eq_comap]
  exact (Subgroup.le_normalizer_comap (H := (matrixHom K).range) (Folded K).subtype)
    (folded_weyl_mem_radical_normalizer K n)

end SymmetricSubgroupAsymptotics.CFSGFFourBinaryFoldedRadicalNormalizer
