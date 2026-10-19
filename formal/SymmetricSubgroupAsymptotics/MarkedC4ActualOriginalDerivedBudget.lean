import SymmetricSubgroupAsymptotics.MarkedC4ActualAbelianAwareNormalBudget
import SymmetricSubgroupAsymptotics.SmallPermutationQuotientAbelian

/-! Actual abelian quotient factors have ZERO derived-normal cost. Their
original degrees belong to the abelian block, not to dN. Nonabelian actual
quotients use the ordinary derived-normal quarter bound on originals. -/
set_option autoImplicit false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics.MarkedC4.ActualOriginalDerivedBudget
open RDTDerivedNormalQuarter ActualMarkZeroNormalRank ActualSubdirectFiltration
open ActualAbelianAwareNormalBudget

variable {t : ℕ} (F : Fin t → Type) [∀ i,Group (F i)]

theorem actual_marked_budget (lit : PublishedDerivedNormalQuarterBinary)
    (n : Fin t → ℕ) (G : ∀ i,Subgroup (Equiv.Perm (Fin (n i))))
    (hG : ∀ i,IsPGroup 2 (G i))
    (htrans : ∀ i,∀ x y : Fin (n i),∃ g : G i,g.val x=y)
    [∀ i,Finite (F i)]
    (q : ∀ i,G i →* F i) (onto : ∀ i,Function.Surjective (q i))
    (M : Type) [CommGroup M] [Finite M]
    (A : Subgroup ((∀ i,F i) × M)) (tail : Finset (Fin t))
    (hfull : ∀ i,Function.Surjective ((Pi.evalMonoidHom F i).comp (physical A))) :
    ∀ U : Subgroup A,U.Normal →
      U≤commutator A ⊓ ((ActualQuotientMarkedNormalBudget.tailHom F A tail).comp
        (projection A)).ker →
      normalGen U≤ActualQuotientMarkedNormalBudget.dN tail (effectiveWeight F n) := by
  apply ActualMarkedNormalBudgetTransport.marked_normal_budget A
    (ActualQuotientMarkedNormalBudget.tailHom F A tail)
  intro V hVn hV
  letI : V.Normal := hVn
  have hzero : ∀ i∈tail,∀ x∈V,coordinate F (PhysicalImage A) i x=1 := by
    intro i hi x hx
    have ht : ActualQuotientMarkedNormalBudget.tailHom F A tail x=1 := (hV hx).2
    exact congrFun ht ⟨i,hi⟩
  have hreal := ActualNormalSubdirectFiltration.derived_tail_rank_le F (PhysicalImage A) V
    (ActualQuotientMarkedNormalBudget.physical_image_full F A hfull) tail
    (fun i => (effectiveWeight F n i : ℝ)) (hV.trans inf_le_left) hzero
  apply Nat.le_floor
  apply hreal
  intro i W hWn hW
  letI : W.Normal := hWn
  by_cases hab : ∀ x y : F i,x*y=y*x
  · letI : CommGroup (F i) := { (inferInstance : Group (F i)) with mul_comm := hab }
    have hc : commutator (F i)=⊥ := commutator_eq_bot (F i)
    have hbot : W=⊥ := bot_unique (hW.trans_eq hc)
    simp only [effectiveWeight,if_pos hab,Nat.cast_zero,zero_div,hbot,normalGen_bot]
    norm_num
  · simp only [effectiveWeight,if_neg hab]
    exact ActualDerivedNormalQuotientLift.original_budget_descends (q i) (onto i)
      ((n i : ℝ)/4)
      (fun N hN hderived => original_bound lit (n i) (G i) (SmallPermutationQuotient.two_lt_degree (G i) (q i) (onto i) hab) (hG i) (htrans i) N hN hderived)
      W hW

end SymmetricSubgroupAsymptotics.MarkedC4.ActualOriginalDerivedBudget
