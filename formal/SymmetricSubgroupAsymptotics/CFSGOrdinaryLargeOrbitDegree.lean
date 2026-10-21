import SymmetricSubgroupAsymptotics.CFSGOrdinarySubgroupUpperReduction
import SymmetricSubgroupAsymptotics.MarkedC4LargeOrbitOrdinaryGeneration

/-! Support-sensitive ordinary large-orbit reduction. The length is paid
by the number of ACTUAL large points, not by the original whole degree.
The retained kernel fixes all these same points. This distinction is needed
to keep the exact quadratic coefficient in an ordinary counting theorem. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Classical BigOperators
namespace SymmetricSubgroupAsymptotics.CFSGOrdinaryLargeOrbitDegree
open MarkedC4 ActualLargeOrbitKernel ActualLargeOrbitImage LargeOrbitOrdinaryGeneration

/-- The ordinary generator theorem is applied before enlarging the degree.
The actual range and actual kernel of the large-point projection are kept. -/
theorem exists_cutoff_relative_tuples_by_large_degree
    (h62 : PublishedProposition62) (rate : ℝ) (hrate : 0<rate) :
    ∃ C : ℕ,2≤C ∧ ∀ (b : ℕ) (G : Subgroup (PermutationGroup b)) [IsSolvable G],
      ∃ t : Fin (⌈rate*(Nat.card (largePoints G C) : ℝ)⌉₊) → G,
        Subgroup.closure (Set.range t∪(projection G C).ker)=⊤ := by
  obtain ⟨C,hC,hgen⟩ := h62 rate hrate
  refine ⟨C,hC,?_⟩
  intro b G _
  letI : Fintype (largePoints G C) := Fintype.ofFinite _
  letI : IsSolvable (projection G C).range := image_solvable G
  have hrank := hgen (largePoints G C) (projection G C).range
    (fun x _ => orbit_lower G C x)
  obtain ⟨S,hS,hclose⟩ := genRank_spec (G := (projection G C).range)
  apply ActualLargeOrbitRelative.exists_relative_tuple C G
  refine ⟨S,?_,hclose⟩
  have hsR : (S.card : ℝ)≤(⌈rate*(Nat.card (largePoints G C) : ℝ)⌉₊ : ℝ) := by
    rw [hS]
    apply hrank.trans
    simpa only [Nat.card_eq_fintype_card] using Nat.le_ceil (rate*(Nat.card (largePoints G C) : ℝ))
  exact_mod_cast hsR

/-- Transport only the Fin-index set, preserving the whole actual tuple
range. No rewrite is performed through a dependent Set.range expression. -/
theorem reindex_relative_tuple {G : Type} [Group G] (K : Subgroup G)
    {a l : ℕ} (h : a=l) (t : Fin a → G)
    (ht : Subgroup.closure (Set.range t∪K)=⊤) :
    ∃ u : Fin l → G,Subgroup.closure (Set.range u∪K)=⊤ := by
  let e : Fin a ≃ Fin l := Equiv.cast (congrArg Fin h)
  refine ⟨t ∘ e.symm,?_⟩
  rw [e.symm.surjective.range_comp]
  exact ht

/-- Targets remember an actual set of fixed original points. They are not
silently counted as arbitrary bounded-orbit groups of the whole degree. -/
def FixedPointsWitness (b m : ℕ) (K : Subgroup (PermutationGroup b)) : Prop :=
  ∃ T : Set (Fin b),Nat.card T=m ∧ ∀ x∈T,∀ g∈K,g x=x

abbrev RetainedTargets (C b m : ℕ) :=
  {K : Subgroup (PermutationGroup b) // IsSolvable K ∧
    OrbitCutoffFamilies.OrbitCutoff C K ∧ FixedPointsWitness b m K}

/-- Each fixed-container, fixed-large-degree family has an injective code
in the SAME supported kernels and tuples of length ceil(rate*m). -/
theorem family_card_le_supported_kernel_mul_power
    {C b m : ℕ} {rate : ℝ}
    (hC : 2≤C) (D : Subgroup (PermutationGroup b))
    (htuple : ∀ G : Subgroup (PermutationGroup b),IsSolvable G →
      ∃ t : Fin (⌈rate*(Nat.card (largePoints G C) : ℝ)⌉₊) → G,
        Subgroup.closure (Set.range t∪(projection G C).ker)=⊤) :
    Nat.card {G : Subgroup (PermutationGroup b) //
      IsSolvable G ∧ G≤D ∧ Nat.card (largePoints G C)=m} ≤
      Nat.card (RetainedTargets C b m) * Nat.card D^(⌈rate*(m : ℝ)⌉₊) := by
  let A := {G : Subgroup (PermutationGroup b) //
    IsSolvable G ∧ G≤D ∧ Nat.card (largePoints G C)=m}
  apply CFSGOrdinarySubgroupUpperReduction.family_card_le_core_mul_power D
    (fun G : A => G.val) Subtype.val_injective (fun G => G.property.2.1)
    (fun K => IsSolvable K ∧ OrbitCutoffFamilies.OrbitCutoff C K ∧ FixedPointsWitness b m K)
  intro G
  letI : IsSolvable G.val := G.property.1
  obtain ⟨t,ht⟩ := htuple G.val G.property.1
  have hm := G.property.2.2
  have hlen : ⌈rate*(Nat.card (largePoints G.val C) : ℝ)⌉₊=⌈rate*(m : ℝ)⌉₊ :=
    congrArg (fun a : ℕ => ⌈rate*(a : ℝ)⌉₊) hm
  obtain ⟨u,hu⟩ := reindex_relative_tuple (projection G.val C).ker hlen t ht
  let S : Finset G.val := Finset.univ.image u
  refine ⟨(projection G.val C).ker,S,?_,?_,?_⟩
  · refine ⟨(solubleTarget G.val C hC).property.1,
      (solubleTarget G.val C hC).property.2,?_⟩
    refine ⟨(largePoints G.val C : Set (Fin b)),hm,?_⟩
    intro x hx g hg
    exact fixes_large G.val C hx hg
  · exact (Finset.card_image_le).trans (by simp)
  · simpa only [S,Finset.coe_image,Finset.coe_univ,Set.image_univ] using hu

/-- The lost quadratic budget pays all large-point generators at rate1/32.
This estimate remains valid at either empty endpoint of the support split. -/
theorem large_tuple_quadratic_budget (n m : ℝ) (hm : 0 ≤ m) (hmn : m≤n) :
    2*n*((1/32)*m) ≤ (n^2-(n-m)^2)/16 := by
  nlinarith [mul_nonneg hm (sub_nonneg.mpr hmn)]

end SymmetricSubgroupAsymptotics.CFSGOrdinaryLargeOrbitDegree
