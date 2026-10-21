import SymmetricSubgroupAsymptotics.BinaryPairRegularKernelSplit
import SymmetricSubgroupAsymptotics.BinaryHeisenbergEightOffsetGauge

/-! The same original Heisenberg-top K14 extension becomes its literal
zero-offset action by a physical point conjugation. Actual derived-word
values, not a split-extension premise, supply the sparse constraints. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.BinaryPairFrame

open BinaryHeisenbergEightSquareCarry HeisenbergCarries

variable {X : Type} {U : Subgroup (Equiv.Perm X)} (F : BinaryPairFrame U (Fin 8))

/-- Full original-action normalization for the second width/rank template. -/
theorem heisenberg14_exists_physical_conjugate_zero_offset_model
    (u : Fin 4 → U)
    (hp : ∀ i, F.top (u i) = originalSelected i)
    (hgen : Subgroup.closure (Set.range fun i => F.top (u i)) = F.top.range)
    (hK : F.kernelSpace = K14)
    (hderived : ∀ k : F.top.ker, (k : U) ∈ commutator U → F.bits k ∈ R14) :
    ∃ a : V, U.map (MulAut.conj (F.physicalFlip a)).toMonoidHom =
      F.affineGeneratedModel F.kernelSpace (fun i => F.top (u i)) (fun _ => 0) := by
  have hsquare (i : Fin 4) : squareMap i (actualOffsets F u) ∈ K14 := by
    rw [squareMap_actualOffsets F u hp, ← hK]
    exact ⟨Additive.ofMul _, rfl⟩
  have hrelator (r : Fin 11) : relatorMap r (actualOffsets F u) ∈ R14 := by
    rw [relatorMap_actualOffsets F u hp]
    exact hderived _ (actualRelator_mem_commutator F u hp r)
  obtain ⟨a, ha⟩ := BinaryHeisenbergEightOffsetGauge.exists_source_orientation
    (actualOffsets F u) hsquare hrelator
  refine ⟨a, F.physical_conjugate_eq_zero_offset_model_of_source_orientation u hgen a ?_⟩
  intro i
  rw [hK]
  have hi := ha i
  rw [unflatten_actualOffsets] at hi
  simpa only [hp] using hi

end SymmetricSubgroupAsymptotics.BinaryPairFrame
