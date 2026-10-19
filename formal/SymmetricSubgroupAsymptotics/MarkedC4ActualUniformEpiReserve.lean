import SymmetricSubgroupAsymptotics.MarkedC4ActualUniversalEpiReserve
import SymmetricSubgroupAsymptotics.MarkedC4ActualUniformSourceRank

/-! One uniform per-peel polynomial for a fixed initial physical degree B.
All actual suffix source ranks are derived; P(r) does not occur in this
factor and therefore is never multiplied along the excessive history. -/
set_option autoImplicit false
noncomputable section
open scoped Classical BigOperators
namespace SymmetricSubgroupAsymptotics.MarkedC4.ActualUniformEpiReserve
open ActualAbelianFactorSplit RDTOriginalWordStructure RDTExcessStructure RDTNormalFInterface
open ActualNormalFMarkedPeel ActualMarkZeroNormalRank

def peelFactor (lit : RDTTheorem46BinaryInput) (C B r : ℕ) : ℝ :=
  max (kappa3 lit (2+C)) 1*((B : ℝ)+r+2)^kappa4 lit (2+C)

theorem actual_epi_le_uniform_reserve
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
      (e=1 ∧ ∀ i,¬Abelian F i →¬HasExcess (G i) (n i) 2))
    (B : ℕ) (hB : (∑ i : Fin t,(n i : ℝ))≤(B : ℝ)) :
    (Nat.card {f : A →* Q // Function.Surjective f} : ℝ)≤
      peelFactor lit C B r*
        (2 : ℝ)^(markedF ((∑ i : Fin t,(n i : ℝ))+w) r-
          markedF (∑ i : Fin t,(n i : ℝ)) r) := by
  have hcount := ActualUniversalEpiReserve.actual_epi_le_reserve hKP h55 hderived lit
    n G C hcut hG htrans F q onto r A hfull Q hQ hQcard TQ hTQ e w hexcess hzcap hbranch
  have hrank := ActualUniformSourceRank.rank_le_degree_add_marks hKP h55
    n G C hcut hG htrans F q onto r A hfull
  have hrankB : (genRank A : ℝ)≤(B : ℝ)+r+2 := by linarith
  have hp : kappa3 lit (2+C)*(genRank A : ℝ)^kappa4 lit (2+C)≤peelFactor lit C B r := by
    unfold peelFactor
    apply mul_le_mul (le_max_left _ _)
      (Real.rpow_le_rpow (Nat.cast_nonneg _) hrankB (kappa4_nonneg lit (2+C)))
    · positivity
    · exact (show (0 : ℝ)≤1 by norm_num).trans (le_max_right _ _)
  exact hcount.trans (mul_le_mul_of_nonneg_right hp (by positivity))

end SymmetricSubgroupAsymptotics.MarkedC4.ActualUniformEpiReserve
