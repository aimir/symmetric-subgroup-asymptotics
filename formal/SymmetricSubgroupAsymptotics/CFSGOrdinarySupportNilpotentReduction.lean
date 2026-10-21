import SymmetricSubgroupAsymptotics.CFSGOrdinaryLargeOrbitDegree

/-! The large-orbit kernel is reduced to nilpotent subgroups without
forgetting the same fixed original points. Both generator alphabets stay
inside the same actual soluble container. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Classical BigOperators
namespace SymmetricSubgroupAsymptotics.CFSGOrdinaryLargeOrbitDegree
open MarkedC4
open ActualLargeOrbitKernel

/-- Fixed-point witnesses pass to the actual retained subgroup. -/
theorem FixedPointsWitness.mono {b m : ℕ} {J K : Subgroup (PermutationGroup b)}
    (hJ : FixedPointsWitness b m J) (hK : K≤J) : FixedPointsWitness b m K := by
  obtain ⟨T,hT,hfix⟩ := hJ
  exact ⟨T,hT,fun x hx g hg => hfix x hx g (hK hg)⟩

abbrev NilpotentFixedTargets (b m : ℕ) :=
  {K : Subgroup (PermutationGroup b) // Group.IsNilpotent K ∧ FixedPointsWitness b m K}
abbrev RetainedInside (C b m : ℕ) (D : Subgroup (PermutationGroup b)) :=
  {K : Subgroup (PermutationGroup b) // IsSolvable K ∧
    OrbitCutoffFamilies.OrbitCutoff C K ∧ FixedPointsWitness b m K ∧ K≤D}

/-- All fixed points survive nilpotent-core selection; no new labels are
chosen and no ambient factorial is charged to the supplement. -/
theorem retained_inside_card_le_nilpotent_fixed (C b m : ℕ)
    (D : Subgroup (PermutationGroup b)) :
    Nat.card (RetainedInside C b m D) ≤ Nat.card (NilpotentFixedTargets b m) *
      Nat.card D^(OrdinaryNilpotentGeneration.nilpotentControlCutoff C*Nat.sqrt (2*b)) := by
  apply CFSGOrdinarySubgroupUpperReduction.family_card_le_core_mul_power D
    (fun K : RetainedInside C b m D => K.val) Subtype.val_injective
    (fun K => K.property.2.2.2)
    (fun K => Group.IsNilpotent K ∧ FixedPointsWitness b m K)
  intro J
  letI : IsSolvable J.val := J.property.1
  obtain ⟨K,S,hK,hS,hgen⟩ := OrdinaryNilpotentGeneration.bounded_orbit_nilpotent_core_generation
    KovacsPraegerAbelianizationProof.kovacsPraegerAbelianizationBound J.val J.property.2.1
  refine ⟨K,S,⟨?_,?_⟩,hS,hgen⟩
  · letI := hK
    exact Group.nilpotent_of_mulEquiv
      (K.equivMapOfInjective J.val.subtype Subtype.val_injective)
  · apply J.property.2.2.1.mono
    rintro _ ⟨k,hk,rfl⟩
    exact k.property

/-- Fixed-large-degree sources reduce to the literal kernels inside D,
so the next stage still uses the small soluble-container alphabet. -/
theorem family_card_le_retained_inside_mul_power
    {C b m : ℕ} {rate : ℝ} (hC : 2≤C)
    (D : Subgroup (PermutationGroup b))
    (htuple : ∀ G : Subgroup (PermutationGroup b),IsSolvable G →
      ∃ t : Fin (⌈rate*(Nat.card (largePoints G C) : ℝ)⌉₊) → G,
        Subgroup.closure (Set.range t∪(projection G C).ker)=⊤) :
    Nat.card {G : Subgroup (PermutationGroup b) //
      IsSolvable G ∧ G≤D ∧ Nat.card (largePoints G C)=m} ≤
      Nat.card (RetainedInside C b m D) * Nat.card D^(⌈rate*(m : ℝ)⌉₊) := by
  let A := {G : Subgroup (PermutationGroup b) //
    IsSolvable G ∧ G≤D ∧ Nat.card (largePoints G C)=m}
  apply CFSGOrdinarySubgroupUpperReduction.family_card_le_core_mul_power D
    (fun G : A => G.val) Subtype.val_injective (fun G => G.property.2.1)
    (fun K => IsSolvable K ∧ OrbitCutoffFamilies.OrbitCutoff C K ∧
      FixedPointsWitness b m K ∧ K≤D)
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
      (solubleTarget G.val C hC).property.2,?_,?_⟩
    · exact ⟨(largePoints G.val C : Set (Fin b)),hm,
        fun _ hx _ hg => fixes_large G.val C hx hg⟩
    · exact (retained_le G.val C).trans G.property.2.1
  · exact (Finset.card_image_le).trans (by simp)
  · simpa only [S,Finset.coe_image,Finset.coe_univ,Set.image_univ] using hu

/-- A genuine two-stage ordinary count with a support-sensitive nilpotent
core. Only the final sharp count of these smaller supported nilpotent
sources remains; neither stage uses the all-subgroup upper theorem. -/
theorem family_card_le_nilpotent_fixed_mul_power
    {C b m : ℕ} {rate : ℝ} (hC : 2≤C)
    (D : Subgroup (PermutationGroup b))
    (htuple : ∀ G : Subgroup (PermutationGroup b),IsSolvable G →
      ∃ t : Fin (⌈rate*(Nat.card (largePoints G C) : ℝ)⌉₊) → G,
        Subgroup.closure (Set.range t∪(projection G C).ker)=⊤) :
    Nat.card {G : Subgroup (PermutationGroup b) //
      IsSolvable G ∧ G≤D ∧ Nat.card (largePoints G C)=m} ≤
      Nat.card (NilpotentFixedTargets b m) *
        Nat.card D^(OrdinaryNilpotentGeneration.nilpotentControlCutoff C*Nat.sqrt (2*b)+
          ⌈rate*(m : ℝ)⌉₊) := by
  calc
    _ ≤ Nat.card (RetainedInside C b m D) * Nat.card D^(⌈rate*(m : ℝ)⌉₊) :=
      family_card_le_retained_inside_mul_power hC D htuple
    _ ≤ (Nat.card (NilpotentFixedTargets b m) *
        Nat.card D^(OrdinaryNilpotentGeneration.nilpotentControlCutoff C*Nat.sqrt (2*b))) *
          Nat.card D^(⌈rate*(m : ℝ)⌉₊) :=
      Nat.mul_le_mul_right _ (retained_inside_card_le_nilpotent_fixed C b m D)
    _ = _ := by rw [pow_add]; ring

end SymmetricSubgroupAsymptotics.CFSGOrdinaryLargeOrbitDegree
