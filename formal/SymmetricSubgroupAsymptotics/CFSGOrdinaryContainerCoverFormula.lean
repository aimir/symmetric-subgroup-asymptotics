import SymmetricSubgroupAsymptotics.CFSGOrdinarySubgroupFiniteFormula

/-! Any finite cover by ACTUAL soluble containers suffices for ordinary
counting. Maximality, a conjugacy-class theorem and the sharp Pyber bound are
not required. This accepts directly a constructed affine/wreath envelope
menu, while Dixon supplies the alphabet order internally. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Classical BigOperators
namespace SymmetricSubgroupAsymptotics.CFSGOrdinaryContainerCoverFormula
open MarkedC4 CFSGOrdinaryLargeOrbitDegree CFSGOrdinarySubgroupUpperReduction
open CFSGOrdinarySubgroupFiniteFormula LargeOrbitOrdinaryGeneration ActualLargeOrbitKernel

/-- The only data of a structural soluble-container construction needed
by the counting reduction. This is actual group containment, not an
ordinary or marked subgroup-counting estimate. -/
structure SolubleContainerCover (b : ℕ) where
  Index : Type
  finiteIndex : Finite Index
  group : Index → Subgroup (PermutationGroup b)
  soluble : ∀ i,IsSolvable (group i)
  covers : ∀ G : Subgroup (PermutationGroup b),IsSolvable G → ∃ i,G≤group i

attribute [instance] SolubleContainerCover.finiteIndex

/-- No maximal-transitive-soluble representative theorem is needed for
the ordinary reduction. The coefficient of a constructed finite menu is
paid once, and every tuple remains inside its SAME actual container. -/
theorem subgroup_card_le_of_container_cover
    (hAG : PublishedAschbacherGuralnickSolubleGeneration)
    (h62 : PublishedProposition62) (rate : ℝ) (hrate : 0<rate) :
    ∃ C : ℕ,2≤C ∧ ∀ (b : ℕ) (E : SolubleContainerCover b),
      Nat.card (Subgroup (PermutationGroup b)) ≤
        b.factorial * Nat.card E.Index *
          ∑ m : Fin (b+1),2^b*Nat.card (NilpotentSources (b-m.val)) *
            (2^(2*b))^(OrdinaryNilpotentGeneration.nilpotentControlCutoff C*Nat.sqrt (2*b)+
              ⌈rate*(m.val : ℝ)⌉₊) := by
  obtain ⟨C,hC,ht⟩ := exists_cutoff_relative_tuples_by_large_degree h62 rate hrate
  refine ⟨C,hC,?_⟩
  intro b E
  letI : Fintype E.Index := Fintype.ofFinite _
  let M := ∑ m : Fin (b+1),2^b*Nat.card (NilpotentSources (b-m.val)) *
    (2^(2*b))^(OrdinaryNilpotentGeneration.nilpotentControlCutoff C*Nat.sqrt (2*b)+
      ⌈rate*(m.val : ℝ)⌉₊)
  have hc := family_card_le_sum_inside (fun G : Subgroup (PermutationGroup b) => IsSolvable G)
    E.group E.covers
  have hi (i : E.Index) :
      Nat.card {G : Subgroup (PermutationGroup b) // IsSolvable G ∧ G≤E.group i}≤M := by
    apply inside_card_le_nilpotent_convolution hC (E.group i)
    · letI : IsSolvable (E.group i) := E.soluble i
      simpa only [Fintype.card_fin] using SolubleContainerOrder.factor_order
        ElementaryDixonOrderProof.WithoutCatalogue.dixonOrder_of_primitive_inputs (Fin b) (E.group i)
    · intro G hG
      letI : IsSolvable G := hG
      exact ht b G
  have hsol : Nat.card {G : Subgroup (PermutationGroup b) // IsSolvable G}≤Nat.card E.Index*M := by
    apply hc.trans
    calc
      _ ≤ ∑ _i : E.Index,M := Finset.sum_le_sum (fun i _ => hi i)
      _ = _ := by simp [Nat.card_eq_fintype_card]
  have horder : Nat.card (PermutationGroup b)=b.factorial := by
    simp only [PermutationGroup,Nat.card_eq_fintype_card,Fintype.card_perm,Fintype.card_fin]
  have hall := subgroup_card_le_card_mul_soluble hAG (PermutationGroup b)
  rw [horder] at hall
  exact hall.trans (by simpa [M,Nat.mul_assoc] using Nat.mul_le_mul_left b.factorial hsol)

end SymmetricSubgroupAsymptotics.CFSGOrdinaryContainerCoverFormula
