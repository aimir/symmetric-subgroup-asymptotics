import SymmetricSubgroupAsymptotics.CFSGNilpotentBoundedSupportRestriction
import SymmetricSubgroupAsymptotics.CFSGOrdinaryContainerCoverFormula

/-! The final ordinary finite reduction uses only fixed-cutoff nilpotent
counts. The SAME cutoff is inherited by the actual core and survives deleting
its actual fixed points. Global nilpotent Theorem3 is not needed. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Classical BigOperators
namespace SymmetricSubgroupAsymptotics.CFSGOrdinaryBoundedNilpotentFormula
open MarkedC4 CFSGOrdinaryLargeOrbitDegree CFSGOrdinarySubgroupUpperReduction
open CFSGOrdinarySubgroupFiniteFormula CFSGOrdinaryContainerCoverFormula
open CFSGNilpotentBoundedSupportRestriction LargeOrbitOrdinaryGeneration ActualLargeOrbitKernel

/-- Actual core selection retains both the orbit cutoff and the original
fixed set. Only the core and tuple are counted. -/
theorem retained_inside_card_le_bounded_fixed (C b m : ℕ)
    (D : Subgroup (PermutationGroup b)) :
    Nat.card (RetainedInside C b m D) ≤ Nat.card (BoundedNilpotentFixedTargets C b m) *
      Nat.card D^(OrdinaryNilpotentGeneration.nilpotentControlCutoff C*Nat.sqrt (2*b)) := by
  apply family_card_le_core_mul_power D
    (fun J : RetainedInside C b m D => J.val) Subtype.val_injective
    (fun J => J.property.2.2.2)
    (fun K => Group.IsNilpotent K ∧ OrbitCutoffFamilies.OrbitCutoff C K ∧ FixedPointsWitness b m K)
  intro J
  letI : IsSolvable J.val := J.property.1
  obtain ⟨K,S,hK,hS,hgen⟩ := OrdinaryNilpotentGeneration.bounded_orbit_nilpotent_core_generation
    KovacsPraegerAbelianizationProof.kovacsPraegerAbelianizationBound J.val J.property.2.1
  have hle : K.map J.val.subtype≤J.val := by
    rintro _ ⟨k,_,rfl⟩
    exact k.property
  refine ⟨K,S,⟨?_,J.property.2.1.mono hle,J.property.2.2.1.mono hle⟩,hS,hgen⟩
  letI := hK
  exact Group.nilpotent_of_mulEquiv (K.equivMapOfInjective J.val.subtype Subtype.val_injective)

theorem inside_card_le_bounded_nilpotent_convolution
    {C b : ℕ} {rate : ℝ} (hC : 2≤C) (D : Subgroup (PermutationGroup b))
    (hD : Nat.card D≤2^(2*b))
    (htuple : ∀ G : Subgroup (PermutationGroup b),IsSolvable G →
      ∃ t : Fin (⌈rate*(Nat.card (largePoints G C) : ℝ)⌉₊) → G,
        Subgroup.closure (Set.range t∪(projection G C).ker)=⊤) :
    Nat.card {G : Subgroup (PermutationGroup b) // IsSolvable G ∧ G≤D} ≤
      ∑ m : Fin (b+1),2^b*Nat.card (OrbitCutoffFamilies.NilpotentFamily C (b-m.val)) *
        (2^(2*b))^(OrdinaryNilpotentGeneration.nilpotentControlCutoff C*Nat.sqrt (2*b)+
          ⌈rate*(m.val : ℝ)⌉₊) := by
  apply (inside_card_le_sum_large_degree C b D).trans
  apply Finset.sum_le_sum
  intro m _
  apply (family_card_le_retained_inside_mul_power hC D htuple).trans
  calc
    _ ≤ (Nat.card (BoundedNilpotentFixedTargets C b m.val) *
        Nat.card D^(OrdinaryNilpotentGeneration.nilpotentControlCutoff C*Nat.sqrt (2*b))) *
          Nat.card D^(⌈rate*(m.val : ℝ)⌉₊) :=
      Nat.mul_le_mul_right _ (retained_inside_card_le_bounded_fixed C b m.val D)
    _ = Nat.card (BoundedNilpotentFixedTargets C b m.val) *
        Nat.card D^(OrdinaryNilpotentGeneration.nilpotentControlCutoff C*Nat.sqrt (2*b)+
          ⌈rate*(m.val : ℝ)⌉₊) := by rw [pow_add]; ring
    _ ≤ _ := Nat.mul_le_mul (bounded_fixed_card_le C b m.val) (Nat.pow_le_pow_left hD _)

/-- All subgroup counts reduce to a finite soluble envelope menu and only
BOUNDED nilpotent counts on the smaller physical complement. The source
ordinary upper theorem and T1 are not used anywhere in this proof. -/
theorem subgroup_card_le_bounded_nilpotent_convolution
    (hAG : PublishedAschbacherGuralnickSolubleGeneration)
    (h62 : PublishedProposition62) (rate : ℝ) (hrate : 0<rate) :
    ∃ C : ℕ,2≤C ∧ ∀ (b : ℕ) (E : SolubleContainerCover b),
      Nat.card (Subgroup (PermutationGroup b)) ≤
        b.factorial * Nat.card E.Index *
          ∑ m : Fin (b+1),2^b*Nat.card (OrbitCutoffFamilies.NilpotentFamily C (b-m.val)) *
            (2^(2*b))^(OrdinaryNilpotentGeneration.nilpotentControlCutoff C*Nat.sqrt (2*b)+
              ⌈rate*(m.val : ℝ)⌉₊) := by
  obtain ⟨C,hC,ht⟩ := exists_cutoff_relative_tuples_by_large_degree h62 rate hrate
  refine ⟨C,hC,?_⟩
  intro b E
  letI : Fintype E.Index := Fintype.ofFinite _
  let M := ∑ m : Fin (b+1),2^b*Nat.card (OrbitCutoffFamilies.NilpotentFamily C (b-m.val)) *
    (2^(2*b))^(OrdinaryNilpotentGeneration.nilpotentControlCutoff C*Nat.sqrt (2*b)+
      ⌈rate*(m.val : ℝ)⌉₊)
  have hc := family_card_le_sum_inside (fun G : Subgroup (PermutationGroup b) => IsSolvable G)
    E.group E.covers
  have hi (i : E.Index) :
      Nat.card {G : Subgroup (PermutationGroup b) // IsSolvable G ∧ G≤E.group i}≤M := by
    apply inside_card_le_bounded_nilpotent_convolution hC (E.group i)
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

end SymmetricSubgroupAsymptotics.CFSGOrdinaryBoundedNilpotentFormula
