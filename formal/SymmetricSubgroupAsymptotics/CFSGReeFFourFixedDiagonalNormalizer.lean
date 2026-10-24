import SymmetricSubgroupAsymptotics.CFSGReeFFourPairedWordDiagonalNormalization
import SymmetricSubgroupAsymptotics.CFSGReeFFourUniqueFixedInversionCover
import SymmetricSubgroupAsymptotics.CFSGReeFFourPositiveDiagonalCentralizer
import SymmetricSubgroupAsymptotics.CFSGReeFFourBorelIntersection

/-! Actual diagonal-normalizing elements of the original fixed Ree
source have no positive or inversion factors. All hypotheses of the
shared unique-Bruhat lemma are discharged in this same group. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGReeFFourFixedDiagonalNormalizer
open CFSGReeFFourFixedModelEquivalence CFSGReeFFourFixedPositiveFamilies
open CFSGReeFFourOppositionFixedPositiveNegative CFSGReeFFourFixedBruhatCover
open CFSGReeFFourBorelIntersection CFSGReeFFourPairedWordDiagonalNormalization
open CFSGReeFFourUniqueFixedInversionCover CFSGReeFFourPositiveDiagonalCentralizer
open CFSGOpposedSubgroupPeeling CFSGUniqueBruhatDiagonalNormalizer

private theorem inversion_normalized {G : Type*} [Group G] (U V D : Subgroup G) (w : G)
    (hDU : D≤Subgroup.normalizer (U : Set G))
    (hDV : D≤Subgroup.normalizer (V : Set G))
    (hw : w∈Subgroup.normalizer (D : Set G)) :
    D≤Subgroup.normalizer (inversionPart U V w : Set G) := by
  intro d hd
  apply Subgroup.inf_normalizer_le_normalizer_inf
  refine ⟨hDU hd,?_⟩
  apply Subgroup.le_normalizer_comap (MulAut.conj w).toMonoidHom
  exact hDV ((Subgroup.mem_normalizer_iff.mp hw d).mp hd)

private theorem diagonal_le_positive_normalizer (m : ℕ) :
    fixedDiagonal m≤Subgroup.normalizer (fixedPositive m : Set (originalModelFixed m)) := by
  rw [fixedDiagonal_eq_pairNormalizer]
  exact inf_le_left

private theorem diagonal_le_negative_normalizer (m : ℕ) :
    fixedDiagonal m≤Subgroup.normalizer (fixedNegative m : Set (originalModelFixed m)) := by
  rw [fixedDiagonal_eq_pairNormalizer]
  exact inf_le_right

theorem fixed_inversion_normalized_by_diagonal (m : ℕ) (w : List Bool) :
    fixedDiagonal m≤Subgroup.normalizer
      (inversionPart (fixedPositive m) (fixedNegative m) (fixedPairedWord m w) : Set (originalModelFixed m)) :=
  inversion_normalized (fixedPositive m) (fixedNegative m) (fixedDiagonal m) (fixedPairedWord m w)
    (diagonal_le_positive_normalizer m) (diagonal_le_negative_normalizer m)
    (fixedPairedWord_normalizes_diagonal m w)

theorem exists_diagonal_paired_word_of_normalizes_diagonal (m : ℕ) (hm : 0<m)
    (g : originalModelFixed m)
    (hg : g∈Subgroup.normalizer (fixedDiagonal m : Set (originalModelFixed m))) :
    ∃ w : List Bool,∃ d∈fixedDiagonal m,g=d*fixedPairedWord m w := by
  obtain ⟨u,hu,d,hd,w,v,hv,hprod⟩ := exists_fixed_inversion_four_factor_cell m g
  refine ⟨w,d,hd,?_⟩
  exact eq_diagonal_word_of_normalizes_diagonal (fixedPositive m) (fixedDiagonal m)
    (inversionPart (fixedPositive m) (fixedNegative m) (fixedPairedWord m w))
    (fixedPairedWord m w) g u d v (diagonal_le_positive_normalizer m)
    (fixed_inversion_normalized_by_diagonal m w) inf_le_left
    (fixedPairedWord_normalizes_diagonal m w) hg
    (fixed_inversion_factorMap_injective m (fixedPairedWord m w))
    (eq_one_of_positive_diagonal_fixed m hm) hu hd hv hprod

end SymmetricSubgroupAsymptotics.CFSGReeFFourFixedDiagonalNormalizer
