import SymmetricSubgroupAsymptotics.CFSGNilpotentSupportRestriction
import SymmetricSubgroupAsymptotics.ElementaryDixonOrderWithoutCatalogue

/-! A support-sensitive finite ordinary counting formula. The only
unestimated subgroup counts on its right are NILPOTENT groups on the
smaller small-point degree b-m. Thus this is not the desired all-subgroup
upper bound repackaged as a hypothesis. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Classical BigOperators
namespace SymmetricSubgroupAsymptotics.CFSGOrdinarySubgroupFiniteFormula
open MarkedC4 CFSGOrdinaryLargeOrbitDegree CFSGOrdinarySubgroupUpperReduction
open CFSGNilpotentSupportRestriction LargeOrbitOrdinaryGeneration ActualLargeOrbitKernel

/-- The actual large-point degree partitions a fixed-container source
family, including the empty large set and the whole original point set. -/
theorem inside_card_le_sum_large_degree (C b : ℕ) (D : Subgroup (PermutationGroup b)) :
    Nat.card {G : Subgroup (PermutationGroup b) // IsSolvable G ∧ G≤D} ≤
      ∑ m : Fin (b+1),Nat.card {G : Subgroup (PermutationGroup b) //
        IsSolvable G ∧ G≤D ∧ Nat.card (largePoints G C)=m.val} := by
  let A := {G : Subgroup (PermutationGroup b) // IsSolvable G ∧ G≤D}
  let B (m : Fin (b+1)) := {G : Subgroup (PermutationGroup b) //
    IsSolvable G ∧ G≤D ∧ Nat.card (largePoints G C)=m.val}
  let code : A → Σ m : Fin (b+1),B m := fun G =>
    ⟨⟨Nat.card (largePoints G.val C),by
      have h := ActualLargeOrbitImage.degree_le G.val C
      omega⟩,⟨G.val,G.property.1,G.property.2,rfl⟩⟩
  have hinj : Function.Injective code := by
    intro G H h
    apply Subtype.ext
    exact congrArg (fun z : Σ m : Fin (b+1),B m => z.2.val) h
  exact (Nat.card_le_card_of_injective code hinj).trans_eq (by rw [Nat.card_sigma])

/-- Both short tuples are charged in one actual small-order container;
the nilpotent core retains the actual m fixed original points. -/
theorem inside_card_le_nilpotent_convolution
    {C b : ℕ} {rate : ℝ} (hC : 2≤C) (D : Subgroup (PermutationGroup b))
    (hD : Nat.card D≤2^(2*b))
    (htuple : ∀ G : Subgroup (PermutationGroup b),IsSolvable G →
      ∃ t : Fin (⌈rate*(Nat.card (largePoints G C) : ℝ)⌉₊) → G,
        Subgroup.closure (Set.range t∪(projection G C).ker)=⊤) :
    Nat.card {G : Subgroup (PermutationGroup b) // IsSolvable G ∧ G≤D} ≤
      ∑ m : Fin (b+1),2^b*Nat.card (NilpotentSources (b-m.val)) *
        (2^(2*b))^(OrdinaryNilpotentGeneration.nilpotentControlCutoff C*Nat.sqrt (2*b)+
          ⌈rate*(m.val : ℝ)⌉₊) := by
  apply (inside_card_le_sum_large_degree C b D).trans
  apply Finset.sum_le_sum
  intro m _
  apply (family_card_le_nilpotent_fixed_mul_power hC D htuple).trans
  exact Nat.mul_le_mul (nilpotent_fixed_card_le b m.val) (Nat.pow_le_pow_left hD _)

/-- The independent finite counting reduction needed for RDT Theorem1.
Dixon and bounded nilpotent-core generation are already supplied by proved
project theorems. Remaining estimates concern only the literal soluble
container menu and nilpotent subgroups, plus the ordinary large-orbit
source theorem. No T1 or ordinary all-subgroup count is used. -/
theorem subgroup_card_le_nilpotent_convolution
    (hAG : PublishedAschbacherGuralnickSolubleGeneration)
    (h62 : PublishedProposition62) (rate : ℝ) (hrate : 0<rate) :
    ∃ C : ℕ,2≤C ∧ ∀ b : ℕ,
      Nat.card (Subgroup (PermutationGroup b)) ≤
        b.factorial * Nat.card (SolubleContainerCount.Index (Fin b)) *
          ∑ m : Fin (b+1),2^b*Nat.card (NilpotentSources (b-m.val)) *
            (2^(2*b))^(OrdinaryNilpotentGeneration.nilpotentControlCutoff C*Nat.sqrt (2*b)+
              ⌈rate*(m.val : ℝ)⌉₊) := by
  obtain ⟨C,hC,ht⟩ := exists_cutoff_relative_tuples_by_large_degree h62 rate hrate
  refine ⟨C,hC,?_⟩
  intro b
  let I := SolubleContainerCount.Index (Fin b)
  letI : Fintype I := Fintype.ofFinite _
  let D := SolubleContainerOrder.physicalContainer (Fin b)
  let M := ∑ m : Fin (b+1),2^b*Nat.card (NilpotentSources (b-m.val)) *
    (2^(2*b))^(OrdinaryNilpotentGeneration.nilpotentControlCutoff C*Nat.sqrt (2*b)+
      ⌈rate*(m.val : ℝ)⌉₊)
  have hcover (J : Subgroup (PermutationGroup b)) (hJ : IsSolvable J) : ∃ i : I,J≤D i := by
    letI : IsSolvable J := hJ
    exact SolubleContainerOrder.cover (Fin b) J
  have hc := family_card_le_sum_inside (fun J : Subgroup (PermutationGroup b) => IsSolvable J) D hcover
  have hi (i : I) : Nat.card {G : Subgroup (PermutationGroup b) // IsSolvable G ∧ G≤D i} ≤ M := by
    apply inside_card_le_nilpotent_convolution hC (D i)
    · simpa only [Fintype.card_fin] using SolubleContainerOrder.physicalContainer_order (Fin b)
        ElementaryDixonOrderProof.WithoutCatalogue.dixonOrder_of_primitive_inputs i
    · intro G hG
      letI : IsSolvable G := hG
      exact ht b G
  have hsol : Nat.card {G : Subgroup (PermutationGroup b) // IsSolvable G} ≤ Nat.card I*M := by
    apply hc.trans
    calc
      _ ≤ ∑ _i : I,M := Finset.sum_le_sum (fun i _ => hi i)
      _ = _ := by simp only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul,Nat.card_eq_fintype_card,Nat.cast_id]
  have horder : Nat.card (PermutationGroup b)=b.factorial := by
    simp only [PermutationGroup,Nat.card_eq_fintype_card,Fintype.card_perm,Fintype.card_fin]
  have hall := subgroup_card_le_card_mul_soluble hAG (PermutationGroup b)
  rw [horder] at hall
  exact hall.trans (by simpa [I,M,Nat.mul_assoc] using Nat.mul_le_mul_left b.factorial hsol)

end SymmetricSubgroupAsymptotics.CFSGOrdinarySubgroupFiniteFormula
