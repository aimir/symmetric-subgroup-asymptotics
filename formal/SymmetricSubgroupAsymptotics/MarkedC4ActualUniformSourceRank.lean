import SymmetricSubgroupAsymptotics.MarkedC4ActualOriginalSourceRankPacket
import SymmetricSubgroupAsymptotics.MarkedC4ActualNonabelianTailLabels

/-! The uniform polynomial rank envelope is derived from the SAME
ordinary5.5 source construction; no additional rank literature is needed. -/
set_option autoImplicit false
noncomputable section
open scoped Classical BigOperators
namespace SymmetricSubgroupAsymptotics.MarkedC4.ActualUniformSourceRank
open ActualAbelianFactorSplit RDTOriginalWordStructure

theorem rank_le_degree_add_marks
    (hKP : KovacsPraegerBinaryAbelianQuotientBound) (h55 : PublishedTheorem55Binary)
    {t : ℕ} (n : Fin t → ℕ) (G : ∀ i,Subgroup (Equiv.Perm (Fin (n i))))
    (C : ℕ) (hcut : ∀ i,n i≤C) (hG : ∀ i,IsPGroup 2 (G i))
    (htrans : ∀ i,∀ x y : Fin (n i),∃ g : G i,g.val x=y)
    (F : Fin t → Type) [∀ i,Group (F i)] [∀ i,Finite (F i)]
    (q : ∀ i,G i →* F i) (onto : ∀ i,Function.Surjective (q i))
    (r : ℕ) (A : Subgroup ((∀ i,F i) × ActualGlobalMarkGeneratorRank.Marks r))
    (hfull : ∀ i,Function.Surjective (fun a : A => a.val.1 i)) :
    (genRank A : ℝ)≤(∑ i : Fin t,(n i : ℝ))+r := by
  obtain ⟨tail,_,_,hrank⟩ := ActualOriginalSourceRankPacket.exists_rank_packet
    n G F hKP h55 C hcut hG htrans q onto r A hfull 3 (Or.inl rfl)
  have hpart := ActualNonabelianTailLabels.degree_partition F n tail
  have hd : 0≤dependentDegree (nonabelianWeight F n) tail := by
    apply Finset.sum_nonneg
    intro i hi
    split_ifs <;> positivity
  have ht : 0≤tailDegree (nonabelianWeight F n) tail := by
    apply Finset.sum_nonneg
    intro i hi
    split_ifs <;> positivity
  have ha : 0≤abelianDegree F n :=
    Finset.sum_nonneg (fun _ _ => Nat.cast_nonneg _)
  change (genRank A : ℝ)≤3*dependentDegree (nonabelianWeight F n) tail/4+
    (tailDegree (nonabelianWeight F n) tail+abelianDegree F n)/2+r at hrank
  linarith

end SymmetricSubgroupAsymptotics.MarkedC4.ActualUniformSourceRank
