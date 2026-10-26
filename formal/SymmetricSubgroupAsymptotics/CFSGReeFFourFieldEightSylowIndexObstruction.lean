import SymmetricSubgroupAsymptotics.CFSGReeFFourConjugatePositiveIndices
import SymmetricSubgroupAsymptotics.CFSGReeFFourFixedPositiveSylow
import SymmetricSubgroupAsymptotics.CFSGReeFFourPerfectProjection
import SymmetricSubgroupAsymptotics.SylowIntersectionDegreeObstruction

/-! The original full-centre quotient has no subgroup of index109.
We use the SAME subgroup's preimage in the original fixed group and its
actual coset action. The full fixed-positive Sylow supplies the modulo8
orbit condition and the actual normalizer quotient49 supplies its fixed
point divisor. No centre-triviality or simplicity assumption is needed. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGReeFFourFieldEightSylowIndexObstruction
open CFSGReeFFourFixedModelEquivalence CFSGReeFFourFixedAmbientHom
open CFSGReeFFourFixedPositiveFamilies CFSGReeFFourFixedPositiveSylow
open CFSGReeFFourConjugatePositiveIndices CFSGReeFFourPerfectProjection
local instance : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩

private instance fixedFinite : Finite (originalModelFixed 1) :=
  Finite.of_injective (fixedAmbientHom 1) (fixedAmbientHom_injective 1)

theorem index_ne_oneOhNine (K : Subgroup (CFSG.Models.ReeF4 1)) : K.index≠109 := by
  classical
  intro hK
  let H : Subgroup (originalModelFixed 1) := K.comap (fixedToOriginal 1 (by omega))
  have hH : H.index=109 :=
    (K.index_comap_of_surjective (fixedToOriginal_surjective 1 (by omega))).trans hK
  let P : Sylow 2 (originalModelFixed 1) := fixedPositiveSylow 1
  have hP : (P : Subgroup (originalModelFixed 1))=fixedPositive 1 :=
    fixedPositiveSylow_coe 1
  have hconj (g : originalModelFixed 1) :
      ((g • P : Sylow 2 (originalModelFixed 1)) : Subgroup (originalModelFixed 1))=
        (fixedPositive 1).map (MulAut.conj g).toMonoidHom := by
    rw [Sylow.coe_subgroup_smul,hP]
    rfl
  have hintersection : ∀ g : originalModelFixed 1,
      (P : Subgroup (originalModelFixed 1)) ⊓
        ((g • P : Sylow 2 (originalModelFixed 1)) : Subgroup (originalModelFixed 1))≠
          (P : Subgroup (originalModelFixed 1)) →
      8 ∣ ((P : Subgroup (originalModelFixed 1)) ⊓
        ((g • P : Sylow 2 (originalModelFixed 1)) : Subgroup (originalModelFixed 1))).relIndex
          (P : Subgroup (originalModelFixed 1)) := by
    intro g hg
    have hproper : positiveIntersection 1 g≠fixedPositive 1 := by
      simpa only [positiveIntersection,hP,hconj] using hg
    have hh := field_dvd_proper_intersection_index 1 g hproper
    simpa only [positiveIntersection,hP,hconj,Nat.reduceMul,Nat.reduceAdd,Nat.reducePow] using hh
  have hnormalizer : (P : Subgroup (originalModelFixed 1)).relIndex
      (Subgroup.normalizer (P : Set (originalModelFixed 1)))=49 := by
    change (P : Subgroup (originalModelFixed 1)).relIndex
      (Subgroup.normalizer ((P : Subgroup (originalModelFixed 1)) : Set (originalModelFixed 1)))=49
    rw [hP]
    have hh := positive_normalizer_relIndex 1
    norm_num only [Nat.reduceMul,Nat.reduceAdd,Nat.reducePow,Nat.reduceSub] at hh
    exact hh
  have hdegree : Nat.card (originalModelFixed 1 ⧸ H)=109 := hH
  exact SylowIntersectionDegreeObstruction.card_ne_oneOhNine_of_eight_and_fortyNine
    (X:=originalModelFixed 1 ⧸ H) P hintersection hnormalizer hdegree

end SymmetricSubgroupAsymptotics.CFSGReeFFourFieldEightSylowIndexObstruction
