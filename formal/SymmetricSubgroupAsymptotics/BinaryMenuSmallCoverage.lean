import SymmetricSubgroupAsymptotics.FinitePermutationRegistry
import SymmetricSubgroupAsymptotics.BinaryMenuCayley2T1
import SymmetricSubgroupAsymptotics.BinaryMenuCayley4T1
import SymmetricSubgroupAsymptotics.BinaryMenuCayley4T2
import SymmetricSubgroupAsymptotics.BinaryMenuCayley4T3
import SymmetricSubgroupAsymptotics.BinaryMenuRoots

/-!
# Complete original-action coverage in widths two and four

This is an end-to-end finite-registry installation on the small domains.
Every transitive binary permutation action is conjugate on its original
points to a committed base-alphabet action. Consequently no normal-state
acceptance is needed in these widths. Widths eight and sixteen are separate.
-/

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
noncomputable section
open scoped Pointwise
namespace SymmetricSubgroupAsymptotics.BinaryMenuSmallCoverage

private def C := BinaryMenuCayley4T3.certificate

def actions4 (i : Fin 3) : Subgroup (Equiv.Perm (Fin 4)) :=
  ![Subgroup.closure (Set.range BinaryMenuCayley4T1.generators),
    Subgroup.closure (Set.range BinaryMenuCayley4T2.generators),
    Subgroup.closure (Set.range BinaryMenuCayley4T3.generators)] i

private def masks4 (k : Fin 3) (i : Fin 8) : Bool :=
  ((#[#[false,true,true,false,true,false,false,true],
     #[true,false,true,false,false,true,false,true],
     #[true,true,true,true,true,true,true,true]] : Array (Array Bool))[k.val]!)[i.val]!

private theorem mask_exact : ∀ k i,
    masks4 k i = true ↔ C.toCayley.elements i ∈ actions4 k := by
  intro k
  fin_cases k
  · intro i
    change masks4 0 i = true ↔ C.toCayley.elements i ∈
      Subgroup.closure (Set.range BinaryMenuCayley4T1.generators)
    rw [BinaryMenuCayley4T1.certificate.mem_closure_iff]
    change _ ↔ ∃ j, BinaryMenuCayley4T1.certificate.rows j =
      permutationCode (C.toCayley.elements i)
    rw [show permutationCode (C.toCayley.elements i) = C.rows i from C.encode_elements i]
    exact (show ∀ i : Fin 8, masks4 0 i = true ↔
      ∃ j, BinaryMenuCayley4T1.certificate.rows j = C.rows i from by decide +kernel) i
  · intro i
    change masks4 1 i = true ↔ C.toCayley.elements i ∈
      Subgroup.closure (Set.range BinaryMenuCayley4T2.generators)
    rw [BinaryMenuCayley4T2.certificate.mem_closure_iff]
    change _ ↔ ∃ j, BinaryMenuCayley4T2.certificate.rows j =
      permutationCode (C.toCayley.elements i)
    rw [show permutationCode (C.toCayley.elements i) = C.rows i from C.encode_elements i]
    exact (show ∀ i : Fin 8, masks4 1 i = true ↔
      ∃ j, BinaryMenuCayley4T2.certificate.rows j = C.rows i from by decide +kernel) i
  · intro i
    constructor
    · intro _
      exact (C.toCayley.mem_closure_iff _).mpr ⟨i,rfl⟩
    · intro _
      exact (show ∀ i : Fin 8, masks4 2 i = true from by decide +kernel) i

private theorem actions_le : ∀ k, actions4 k ≤ Subgroup.closure
    (Set.range BinaryMenuCayley4T3.generators) := by
  intro k
  fin_cases k
  · apply (Subgroup.closure_le _).mpr
    rintro _ ⟨j,rfl⟩
    exact (C.mem_closure_iff _).mpr
      ((show ∀ j, ∃ i, C.rows i = permutationCode (BinaryMenuCayley4T1.generators j)
        from by decide +kernel) j)
  · apply (Subgroup.closure_le _).mpr
    rintro _ ⟨j,rfl⟩
    exact (C.mem_closure_iff _).mpr
      ((show ∀ j, ∃ i, C.rows i = permutationCode (BinaryMenuCayley4T2.generators j)
        from by decide +kernel) j)
  · exact le_rfl

private theorem masks_complete : ∀ selected : Fin 8 → Bool,
    selected C.identity = true →
    (∀ i j, selected i = true → selected j = true → selected (C.rowMul i j) = true) →
    (∀ y : Fin 4, ∃ i, selected i = true ∧ encodedRowAction C i 0 = y) →
    ∃ k, ∀ i, selected i = masks4 k i := by decide +kernel

private theorem root_eq : (BinaryMenuRoot4.sylow : Subgroup (Equiv.Perm (Fin 4))) =
    Subgroup.closure (Set.range BinaryMenuCayley4T3.generators) := by
  rw [BinaryMenuRoot4.sylow_eq]
  have hg : BinaryMenuRoot4.generators = BinaryMenuCayley4T3.generators := by decide +kernel
  rw [hg]

/-- Every transitive binary action on four original points is conjugate to
one of the three original base-alphabet actions C4, V4 and D8. -/
theorem width4_complete (H : Subgroup (Equiv.Perm (Fin 4)))
    (hH : IsPGroup 2 H) (ht : PermutationSubgroupTransitive H) :
    ActionRegistryCovered actions4 H := by
  obtain ⟨g,hg⟩ := pGroup_conjugate_le_chosen_sylow BinaryMenuRoot4.sylow H hH
  rw [root_eq] at hg
  obtain ⟨k,hk⟩ := permutation_registry_of_row_masks C actions4 masks4
    mask_exact actions_le 0 masks_complete (MulAut.conj g • H) hg
    (permutationSubgroupTransitive_conjugate g H ht)
  exact ⟨k,g,hk⟩

/-- The unique transitive binary action on two points is the committed C2. -/
theorem width2_complete (H : Subgroup (Equiv.Perm (Fin 2)))
    (hH : IsPGroup 2 H) (ht : PermutationSubgroupTransitive H) :
    ActionRegistryCovered (fun _ : Unit => Subgroup.closure
      (Set.range BinaryMenuCayley2T1.generators)) H := by
  let C2 := BinaryMenuCayley2T1.certificate
  let acts := fun _ : Unit => Subgroup.closure (Set.range BinaryMenuCayley2T1.generators)
  let masks := fun (_ : Unit) (_ : Fin 2) => true
  obtain ⟨g,hg⟩ := pGroup_conjugate_le_chosen_sylow BinaryMenuRoot2.sylow H hH
  rw [BinaryMenuRoot2.sylow_eq] at hg
  have he : BinaryMenuRoot2.generators = BinaryMenuCayley2T1.generators := by decide +kernel
  rw [he] at hg
  obtain ⟨k,hk⟩ := permutation_registry_of_row_masks C2 acts masks
    (fun _ i => by
      constructor
      · intro _; exact (C2.toCayley.mem_closure_iff _).mpr ⟨i,rfl⟩
      · intro _; rfl)
    (fun _ => le_rfl) 0
    (by decide +kernel) (MulAut.conj g • H) hg
    (permutationSubgroupTransitive_conjugate g H ht)
  exact ⟨k,g,hk⟩

end SymmetricSubgroupAsymptotics.BinaryMenuSmallCoverage
