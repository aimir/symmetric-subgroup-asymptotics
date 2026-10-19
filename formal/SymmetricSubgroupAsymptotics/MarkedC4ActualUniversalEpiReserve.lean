import SymmetricSubgroupAsymptotics.MarkedC4ActualNonabelianTailLabels
import SymmetricSubgroupAsymptotics.MarkedC4ActualOriginalDerivedBudget
import SymmetricSubgroupAsymptotics.MarkedC4ActualPhysicalEpiReserve

/-! Actual universal one-step marked reserve. The source rank, natural dN,
maximal original tail, degree split, abelian physical block, and R/P source
geometry are all derived. Only ordinary structural literature and actual
original quotient maps / selected-target invariants remain as inputs. -/
set_option autoImplicit false
noncomputable section
open scoped Classical BigOperators
namespace SymmetricSubgroupAsymptotics.MarkedC4.ActualUniversalEpiReserve
open ActualAbelianFactorSplit RDTOriginalWordStructure RDTExcessStructure RDTNormalFInterface
open ActualNormalFMarkedPeel ActualMarkZeroNormalRank ActualNonabelianTailLabels

 theorem actual_epi_le_reserve
    (hKP : KovacsPraegerBinaryAbelianQuotientBound) (h55 : PublishedTheorem55Binary)
    (hderived : RDTDerivedNormalQuarter.PublishedDerivedNormalQuarterBinary)
    (lit : RDTTheorem46BinaryInput)
    {t : ℕ} (n : Fin t → ℕ) (G : ∀ i,Subgroup (Equiv.Perm (Fin (n i))))
    (C : ℕ) (hcut : ∀ i,n i≤C) (hG : ∀ i,IsPGroup 2 (G i))
    (htrans : ∀ i,∀ x y : Fin (n i),∃ g : G i,g.val x=y)
    (F : Fin t → Type) [∀ i,Group (F i)] [∀ i,Finite (F i)]
    (q : ∀ i,G i →* F i) (onto : ∀ i,Function.Surjective (q i))
    (r : ℕ) (A : Subgroup ((∀ i,F i) × ActualGlobalMarkGeneratorRank.Marks r))
    (hfull : ∀ i,Function.Surjective (fun a : A => a.val.1 i))
    (Q : Type) [Group Q] [Finite Q] [Nontrivial Q]
    (hQ : IsPGroup 2 Q) (hQcard : Nat.card Q≤2^(2+C))
    (TQ : Subgroup Q) (hTQ : TQ.Normal) (e w : ℝ)
    (hexcess : commutatorLog TQ+e*centralLog TQ≤w/2) (hzcap : centralLog TQ≤w/4)
    (hbranch : e=3 ∨
      (e=5/4 ∧ ∀ i,¬Abelian F i →¬(HasExcess (G i) (n i) 2 ∧ n i=8)) ∨
      (e=1 ∧ ∀ i,¬Abelian F i →¬HasExcess (G i) (n i) 2)) :
    (Nat.card {f : A →* Q // Function.Surjective f} : ℝ)≤
      kappa3 lit (2+C)*(genRank A : ℝ)^kappa4 lit (2+C)*
        (2 : ℝ)^(markedF ((∑ i : Fin t,(n i : ℝ))+w) r-
          markedF (∑ i : Fin t,(n i : ℝ)) r) := by
  obtain ⟨tail,_,htail,hrank⟩ := ActualOriginalSourceRankPacket.exists_rank_packet
    n G F hKP h55 C hcut hG htrans q onto r A hfull e hbranch
  let S := originalTail F tail
  let b₃ := dependentDegree (nonabelianWeight F n) tail
  let b₄ := tailDegree (nonabelianWeight F n) tail+abelianDegree F n
  let d := ActualQuotientMarkedNormalBudget.dN S
    (ActualAbelianAwareNormalBudget.effectiveWeight F n)
  have hb₃ : 0≤b₃ := by
    apply Finset.sum_nonneg
    intro i hi
    split_ifs <;> positivity
  have hb₄ : 0≤b₄ := by
    apply add_nonneg
    · apply Finset.sum_nonneg
      intro i hi
      split_ifs <;> positivity
    · apply Finset.sum_nonneg
      intro i hi
      exact Nat.cast_nonneg _
  have hwidth : b₃+b₄=((∑ i : Fin t,(n i : ℝ))+w)-w := by
    have hh := degree_partition F n tail
    dsimp [b₃,b₄]
    linarith
  have hsource : (genRank A : ℝ)≤e*b₃/4+b₄/2+r := hrank
  have hd : (d : ℝ)≤b₃/4 := actual_dN_cap F n tail
  have hnraw := ActualOriginalDerivedBudget.actual_marked_budget F hderived n G hG htrans
    q onto (ActualGlobalMarkGeneratorRank.Marks r) A S hfull
  have hnormal : ∀ U : Subgroup A,U.Normal →
      U≤commutator A ⊓ (ActualPhysicalEpiReserve.tailHom F S r A).ker →normalGen U≤d := by
    intro U hUn hU
    apply hnraw U hUn
    intro x hx
    refine ⟨(hU hx).1,?_⟩
    change ActualQuotientMarkedNormalBudget.tailHom F A S (projection A x)=1
    funext i
    have ht : ActualPhysicalEpiReserve.tailHom F S r A x=1 := (hU hx).2
    let j := (Fintype.equivFin (ActualPhysicalTailRegrouping.RightLabels S)) i
    have hj := congrFun ht j
    change x.val.1 (ActualPhysicalTailRegrouping.rightLabel S j).val=1 at hj
    have hji : ActualPhysicalTailRegrouping.rightLabel S j=i :=
      (Fintype.equivFin (ActualPhysicalTailRegrouping.RightLabels S)).symm_apply_apply i
    rw [hji] at hj
    exact hj
  have hbinary : ∀ i,IsPGroup 2 (F i) := fun i => (hG i).of_surjective (q i) (onto i)
  have hcard : ∀ i,Nat.card (F i)≤2^(2+C) := by
    intro i
    have hi := hcut i
    exact (ActualBinaryPhysicalOrderBudget.quotient_card_le (G i) (hG i) (q i) (onto i)).trans
      (pow_le_pow_right₀ (by norm_num : 1≤(2 : ℕ)) (by omega : n i≤2+C))
  have hbound := ActualPhysicalEpiReserve.actual_epi_le_reserve F S r A lit (2+C)
    (by omega) hbinary hcard hfull (tail_full F r A tail htail)
    Q hQ hQcard TQ hTQ d hnormal hb₃ hb₄ hwidth hexcess hzcap hsource hd
  have hw : (((∑ i : Fin t,(n i : ℝ))+w)-w)=(∑ i : Fin t,(n i : ℝ)) := by ring
  simpa only [hw] using hbound

end SymmetricSubgroupAsymptotics.MarkedC4.ActualUniversalEpiReserve
