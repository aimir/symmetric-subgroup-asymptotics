import SymmetricSubgroupAsymptotics.MarkedC4ActualOriginalSourceRankPacket
import SymmetricSubgroupAsymptotics.MarkedC4ActualAbelianAwareNormalBudget

/-! Lift a maximal nonabelian-block tail back to ORIGINAL physical labels.
The actual whole-tail surjection and exact degree partition survive; the
abelian block is not presented as one artificially bounded RDT factor. -/
set_option autoImplicit false
noncomputable section
open scoped Classical BigOperators
namespace SymmetricSubgroupAsymptotics.MarkedC4.ActualNonabelianTailLabels
open ActualAbelianFactorSplit ActualMarkZeroNormalRank RDTOriginalWordStructure

variable {t : ℕ} (F : Fin t → Type) [∀ i,Group (F i)] [∀ i,Finite (F i)]
def physicalLabel (j : Fin (Fintype.card (NonabelianLabels F))) : Fin t := (label F j).val

theorem physicalLabel_injective : Function.Injective (physicalLabel F) := by
  intro i j hij
  have h : label F i=label F j := Subtype.ext hij
  exact (Fintype.equivFin (NonabelianLabels F)).symm.injective h

def originalTail (T : Finset (Fin (Fintype.card (NonabelianLabels F)))) : Finset (Fin t) :=
  T.image (physicalLabel F)

theorem tail_full (r : ℕ)
    (A : Subgroup ((∀ i,F i) × ActualGlobalMarkGeneratorRank.Marks r))
    (T : Finset (Fin (Fintype.card (NonabelianLabels F))))
    (hT : Function.Surjective (tailProjection (NonabelianFactors F)
      (PhysicalImage (ActualOriginalSourceRankPacket.blockSource F r A)) T)) :
    Function.Surjective (fun a : A =>
      (fun i : {i : Fin t // i∈originalTail F T} => a.val.1 i.val)) := by
  intro z
  let z' : ∀ j : {j // j∈T},NonabelianFactors F j.val :=
    fun j => z ⟨physicalLabel F j.val,Finset.mem_image.mpr ⟨j.val,j.property,rfl⟩⟩
  obtain ⟨x,hx⟩ := hT z'
  obtain ⟨b,hb⟩ := x.property
  obtain ⟨a,ha,hab⟩ := b.property
  refine ⟨⟨a,ha⟩,?_⟩
  funext i
  rcases i with ⟨i,hi⟩
  obtain ⟨j,hj,hji⟩ := Finset.mem_image.mp hi
  subst i
  have habj := congrArg
    (fun w : (∀ j,NonabelianFactors F j) × (AbelianBlock F × ActualGlobalMarkGeneratorRank.Marks r) => w.1 j) hab
  have hbj := congrFun hb j
  have hxj := congrFun hx ⟨j,hj⟩
  exact habj.trans (hbj.trans hxj)

/-- All original degrees split into dependent nonabelian degree and
independent nonabelian degree PLUS actual abelian-block degree. -/
theorem degree_partition (n : Fin t → ℕ)
    (T : Finset (Fin (Fintype.card (NonabelianLabels F)))) :
    dependentDegree (nonabelianWeight F n) T+
      (tailDegree (nonabelianWeight F n) T+abelianDegree F n)=
        ∑ i : Fin t,(n i : ℝ) := by
  have hsum : dependentDegree (nonabelianWeight F n) T+
      tailDegree (nonabelianWeight F n) T=
        ∑ j : Fin (Fintype.card (NonabelianLabels F)),(nonabelianWeight F n j : ℝ) := by
    unfold dependentDegree tailDegree
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro j hj
    split_ifs <;> simp
  have he := degree_eq F n
  linarith

theorem mem_originalTail (T : Finset (Fin (Fintype.card (NonabelianLabels F))))
    (j : Fin (Fintype.card (NonabelianLabels F))) :
    physicalLabel F j∈originalTail F T ↔ j∈T := by
  constructor
  · intro hj
    obtain ⟨k,hk,hkj⟩ := Finset.mem_image.mp hj
    exact (physicalLabel_injective F hkj) ▸ hk
  · intro hj
    exact Finset.mem_image.mpr ⟨j,hj,rfl⟩

/-- The actual abelian-aware dN budget is EXACTLY the dependent degree
of the original nonabelian block, divided by four. -/
theorem effective_budget_eq (n : Fin t → ℕ)
    (T : Finset (Fin (Fintype.card (NonabelianLabels F)))) :
    ActualQuotientMarkedNormalBudget.budget (originalTail F T)
      (ActualAbelianAwareNormalBudget.effectiveWeight F n)=
        dependentDegree (nonabelianWeight F n) T/4 := by
  let f : Fin t → ℝ := fun i => if i∈originalTail F T then 0 else
    (ActualAbelianAwareNormalBudget.effectiveWeight F n i : ℝ)/4
  have hs := Fintype.sum_subtype_add_sum_subtype (Abelian F) f
  have ha : (∑ i : AbelianLabels F,f i.val)=0 := by
    apply Finset.sum_eq_zero
    intro i hi
    have hab : ∀ x y : F i.val,x*y=y*x := i.property
    simp only [f,ActualAbelianAwareNormalBudget.effectiveWeight,if_pos hab,Nat.cast_zero,zero_div,ite_self]
  have hn : (∑ i : NonabelianLabels F,f i.val)=
      ∑ j : Fin (Fintype.card (NonabelianLabels F)),
        if j∈T then 0 else (nonabelianWeight F n j : ℝ)/4 := by
    symm
    apply Fintype.sum_equiv (Fintype.equivFin (NonabelianLabels F)).symm
    intro j
    change (if j∈T then 0 else (nonabelianWeight F n j : ℝ)/4)=f (physicalLabel F j)
    have hnon : ¬∀ x y : F (physicalLabel F j),x*y=y*x := (label F j).property
    simp only [f,ActualAbelianAwareNormalBudget.effectiveWeight,if_neg hnon,mem_originalTail]
    rfl
  have ht : (∑ i : Fin t,f i)=∑ j : Fin (Fintype.card (NonabelianLabels F)),
      if j∈T then 0 else (nonabelianWeight F n j : ℝ)/4 := by
    rw [ha,zero_add,hn] at hs
    exact hs.symm
  change (∑ i : Fin t,f i)=_
  rw [ht]
  unfold dependentDegree
  rw [Finset.sum_div]
  apply Finset.sum_congr rfl
  intro j hj
  split_ifs <;> simp

theorem actual_dN_cap (n : Fin t → ℕ)
    (T : Finset (Fin (Fintype.card (NonabelianLabels F)))) :
    (ActualQuotientMarkedNormalBudget.dN (originalTail F T)
      (ActualAbelianAwareNormalBudget.effectiveWeight F n) : ℝ)≤
        dependentDegree (nonabelianWeight F n) T/4 := by
  rw [← effective_budget_eq F n T]
  exact ActualQuotientMarkedNormalBudget.dN_cap (originalTail F T)
    (ActualAbelianAwareNormalBudget.effectiveWeight F n)

end SymmetricSubgroupAsymptotics.MarkedC4.ActualNonabelianTailLabels
