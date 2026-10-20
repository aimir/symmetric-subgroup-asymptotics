import SymmetricSubgroupAsymptotics.MarkedC4ActualOriginalWordAbelianMarkedRank
import SymmetricSubgroupAsymptotics.MarkedC4ActualMaximalOriginalTail
import SymmetricSubgroupAsymptotics.MarkedC4ActualOriginalQuotientCaseI
import SymmetricSubgroupAsymptotics.MarkedC4ActualQuotientMarkedNormalBudget

/-! Construct the original nonabelian pullback and maximal tail for the
SAME actual marked source. The abelian quotient block is constructed first;
ordinary5.5 sees only the retained ORIGINAL nonabelian-factor actions. -/
set_option autoImplicit false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics.MarkedC4.ActualOriginalSourceRankPacket
open ActualAbelianFactorSplit ActualMarkZeroNormalRank RDTOriginalWordStructure RDTExcessStructure
open ActualGlobalMarkGeneratorRank

variable {t : ℕ} (n : Fin t → ℕ)
  (G : ∀ i,Subgroup (Equiv.Perm (Fin (n i))))
  (F : Fin t → Type) [∀ i,Group (F i)] [∀ i,Finite (F i)]
abbrev originalDegree (j : Fin (Fintype.card (NonabelianLabels F))) := n (label F j).val
abbrev Original (j : Fin (Fintype.card (NonabelianLabels F))) := G (label F j).val

def blockSource (r : ℕ) (A : Subgroup ((∀ i,F i) × ActualGlobalMarkGeneratorRank.Marks r)) :=
  A.map (split F (ActualGlobalMarkGeneratorRank.Marks r)).toMonoidHom

def originalMap (q : ∀ i,G i →* F i)
    (j : Fin (Fintype.card (NonabelianLabels F))) : Original n G F j →* NonabelianFactors F j :=
  q (label F j).val

def pullback (q : ∀ i,G i →* F i) (r : ℕ)
    (A : Subgroup ((∀ i,F i) × ActualGlobalMarkGeneratorRank.Marks r)) :=
  ActualOriginalWordPullback.OriginalWord (fun j => ↥(Original n G F j)) (NonabelianFactors F)
    (originalMap n G F q) (PhysicalImage (blockSource F r A))

theorem rank_block_eq (r : ℕ)
    (A : Subgroup ((∀ i,F i) × ActualGlobalMarkGeneratorRank.Marks r)) :
    genRank (blockSource F r A)=genRank A := by
  let e := A.equivMapOfInjective (split F (ActualGlobalMarkGeneratorRank.Marks r)).toMonoidHom
    (split F (ActualGlobalMarkGeneratorRank.Marks r)).injective
  apply le_antisymm
  · exact genRank_le_of_surjective e.toMonoidHom e.surjective
  · exact genRank_le_of_surjective e.symm.toMonoidHom e.symm.surjective

/-- No source rank, maximal tail, pullback, or abelian order is supplied:
all are derived from the original physical quotient maps and ordinary KP/5.5. -/
theorem exists_rank_packet
    (hKP : KovacsPraegerBinaryAbelianQuotientBound) (h55 : PublishedTheorem55Binary)
    (C : ℕ) (hcut : ∀ i,n i≤C) (hG : ∀ i,IsPGroup 2 (G i))
    (htrans : ∀ i,∀ x y : Fin (n i),∃ g : G i,g.val x=y)
    (q : ∀ i,G i →* F i) (onto : ∀ i,Function.Surjective (q i))
    (r : ℕ) (A : Subgroup ((∀ i,F i) × ActualGlobalMarkGeneratorRank.Marks r))
    (hfull : ∀ i,Function.Surjective (fun a : A => a.val.1 i))
    (e : ℝ)
    (hbranch : e=3 ∨
      (e=5/4 ∧ ∀ i,¬Abelian F i →¬(HasExcess (G i) (n i) 2 ∧ n i=8)) ∨
      (e=1 ∧ ∀ i,¬Abelian F i →¬HasExcess (G i) (n i) 2)) :
    ∃ tail : Finset (Fin (Fintype.card (NonabelianLabels F))),
      MaximalTail (fun j => ↥(Original n G F j)) (pullback n G F q r A) tail ∧
      Function.Surjective (tailProjection (NonabelianFactors F)
        (PhysicalImage (blockSource F r A)) tail) ∧
      (genRank A : ℝ)≤e*dependentDegree (originalDegree n F) tail/4+
        (tailDegree (originalDegree n F) tail+abelianDegree F n)/2+r := by
  let B := blockSource F r A
  have hB : ∀ j,Function.Surjective (fun b : B => b.val.1 j) :=
    (ActualAbelianFactorSplit.code F (ActualGlobalMarkGeneratorRank.Marks r) ⟨A,hfull⟩).property
  have hH := ActualQuotientMarkedNormalBudget.physical_image_full (NonabelianFactors F) B hB
  have hon : ∀ j,Function.Surjective (originalMap n G F q j) := fun j => onto (label F j).val
  let L := pullback n G F q r A
  have hL := ActualOriginalWordPullback.original_subdirect (fun j => ↥(Original n G F j))
    (NonabelianFactors F) (originalMap n G F q) hon (PhysicalImage B) hH
  obtain ⟨tail,htail⟩ := ActualMaximalOriginalTail.exists_maximal_tail
    (fun j => ↥(Original n G F j)) L
  have hquot := ActualMaximalOriginalTail.quotient_tail_surjective
    (fun j => ↥(Original n G F j)) (NonabelianFactors F)
    (originalMap n G F q) hon (PhysicalImage B) tail htail.1
  have habelian : ∀ i,Abelian F i →(Nat.card (F i) : ℝ)≤(2 : ℝ)^((n i : ℝ)/2) := by
    intro i hi
    letI : CommGroup (F i) := { (inferInstance : Group (F i)) with mul_comm := hi }
    exact ActualBinaryAbelianBudget.section_card_le hKP (G i) (hG i) (q i) (onto i)
  have hExp : ∀ i,HasExp2 (F i) (2+C) := by
    intro i
    have hi := hcut i
    apply ActualBinaryPhysicalOrderBudget.exponent_of_card_le ((hG i).of_surjective (q i) (onto i))
    exact (ActualBinaryPhysicalOrderBudget.quotient_card_le (G i) (hG i) (q i) (onto i)).trans
      (pow_le_pow_right₀ (by norm_num : 1≤(2 : ℕ)) (by omega : n i≤2+C))
  have hCexp := abelian_exponent F C hExp
  have hCbinary : IsPGroup 2 (AbelianBlock F) := fun x => ⟨2+C,hCexp x⟩
  letI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  letI : ∀ j,Group.IsNilpotent (Original n G F j) := fun j => (hG (label F j).val).isNilpotent
  letI : Group.IsNilpotent L := inferInstance
  have hb : e=3 ∨
      (e=5/4 ∧ ∀ j,j∉tail →¬(HasExcess (Original n G F j) (originalDegree n F j) 2 ∧
        originalDegree n F j=8)) ∨
      (e=1 ∧ ∀ j,j∉tail →¬HasExcess (Original n G F j) (originalDegree n F j) 2) := by
    rcases hbranch with h|⟨h,hno⟩|⟨h,hno⟩
    · exact Or.inl h
    · exact Or.inr (Or.inl ⟨h,fun j _ => hno (label F j).val (label F j).property⟩)
    · exact Or.inr (Or.inr ⟨h,fun j _ => hno (label F j).val (label F j).property⟩)
  have hrank := ActualOriginalWordAbelianMarkedRank.actual_source_rank h55 _
    (originalDegree n F) (Original n G F) (fun j => hG (label F j).val)
    (fun j => htrans (label F j).val) L hL tail htail (AbelianBlock F) hCbinary C r
    hCexp (abelian_order_cap F n habelian) B
    (ActualOriginalWordPullback.quotientMap (fun j => ↥(Original n G F j)) (NonabelianFactors F)
      (originalMap n G F q) (PhysicalImage B))
    (ActualOriginalWordPullback.quotientMap_surjective (fun j => ↥(Original n G F j))
      (NonabelianFactors F) (originalMap n G F q) hon (PhysicalImage B)) e hb
  refine ⟨tail,htail,hquot,?_⟩
  rw [rank_block_eq] at hrank
  exact hrank

end SymmetricSubgroupAsymptotics.MarkedC4.ActualOriginalSourceRankPacket
