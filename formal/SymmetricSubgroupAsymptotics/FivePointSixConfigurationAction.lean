import SymmetricSubgroupAsymptotics.InvariantEmbeddingPermutationAction
import SymmetricSubgroupAsymptotics.BinarySixDeletedRepresentation
import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoPrimitiveSixteenRows18And19Complements

/-! An exact six-label action of S5. The labels are six displayed sets of
four nonidentity powers of five-cycles, acted on by conjugation. The only
finite checks concern these six labels and the original five-point maps.
No identification with PGL2(5), group census, or group-order calculation
is needed for the resulting surjective complement maps. -/

set_option autoImplicit false
noncomputable section
open scoped Classical

namespace SymmetricSubgroupAsymptotics
namespace FivePointSixConfigurationAction

abbrev Source := Equiv.Perm (Fin 5)
abbrev a : Source := BinaryFiveFrameRepresentation.cycle
abbrev t : Source := BinaryFiveFrameRepresentation.transposition

def powers (g : Source) : Finset Source := {g, g ^ 2, g ^ 3, g ^ 4}

def configuration (i : Fin 6) : Finset Source :=
  if i = 5 then powers a else powers (a ^ i.val * (t * a * t) * (a ^ i.val)⁻¹)

def conjugation : Source →* Equiv.Perm (Finset Source) :=
  (InvariantEmbeddingPermutationAction.finsetHom Source).comp
    ((MulAut.toPerm Source).comp (MulAut.conj : Source →* MulAut Source))

def gamma : Equiv.Perm (Fin 6) :=
  Equiv.swap 0 5 * Equiv.swap 1 2 * Equiv.swap 3 4

theorem configuration_injective : Function.Injective configuration := by decide +kernel

theorem cycle_configuration : ∀ i,
    conjugation a (configuration i) = configuration (BinarySixDeletedRepresentation.alpha i) := by
  decide +kernel

theorem swap_configuration : ∀ i,
    conjugation t (configuration i) = configuration (gamma i) := by
  decide +kernel

theorem all_liftable (g : Source) :
    g ∈ InvariantEmbeddingPermutationAction.liftable conjugation configuration := by
  have hle : (⊤ : Subgroup Source) ≤
      InvariantEmbeddingPermutationAction.liftable conjugation configuration := by
    rw [← PrimitiveAffineDegreeTwoPrimitiveSixteenRows18And19Complements.symmetric_generators]
    apply (Subgroup.closure_le _).mpr
    intro p hp
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hp
    rcases hp with rfl | rfl
    · exact ⟨BinarySixDeletedRepresentation.alpha, cycle_configuration⟩
    · exact ⟨gamma, swap_configuration⟩
  exact hle (Subgroup.mem_top g)

def hom : Source →* Equiv.Perm (Fin 6) :=
  InvariantEmbeddingPermutationAction.lift conjugation configuration
    configuration_injective all_liftable

theorem hom_a : hom a = BinarySixDeletedRepresentation.alpha :=
  InvariantEmbeddingPermutationAction.lift_eq conjugation configuration
    configuration_injective all_liftable a _ cycle_configuration

theorem hom_t : hom t = gamma :=
  InvariantEmbeddingPermutationAction.lift_eq conjugation configuration
    configuration_injective all_liftable t _ swap_configuration

def second13 : Source := a ^ 2 * t * (a ^ 2)⁻¹
def commutator : Source := a⁻¹ * t * a * t
def second15 : Source := a ^ 3 * commutator * (a ^ 3)⁻¹

def beta13 : Equiv.Perm (Fin 6) :=
  Equiv.swap 0 1 * Equiv.swap 2 5 * Equiv.swap 3 4
def beta15 : Equiv.Perm (Fin 6) :=
  (Equiv.swap 0 3 * Equiv.swap 3 2) * (Equiv.swap 1 5 * Equiv.swap 5 4)

theorem hom_second13 : hom second13 = beta13 := by
  rw [second13, map_mul, map_mul, map_inv, map_pow, hom_a, hom_t]
  apply Equiv.ext
  intro i
  revert i
  decide +kernel

theorem hom_second15 : hom second15 = beta15 := by
  simp only [second15, commutator, map_mul, map_inv, map_pow, hom_a, hom_t]
  apply Equiv.ext
  intro i
  revert i
  decide +kernel

theorem symmetric_generators : Subgroup.closure ({a, second13} : Set Source) = ⊤ := by
  let H := Subgroup.closure ({a, second13} : Set Source)
  have ha : a ∈ H := Subgroup.subset_closure (by simp)
  have hs : second13 ∈ H := Subgroup.subset_closure (by simp)
  have ht : t ∈ H := by
    have hword := H.mul_mem (H.mul_mem (H.inv_mem (H.pow_mem ha 2)) hs) (H.pow_mem ha 2)
    simpa [second13, mul_assoc] using hword
  apply top_unique
  rw [← PrimitiveAffineDegreeTwoPrimitiveSixteenRows18And19Complements.symmetric_generators]
  apply (Subgroup.closure_le _).mpr
  intro p hp
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hp
  rcases hp with rfl | rfl
  · exact ha
  · exact ht

theorem a_even : a ∈ alternatingGroup (Fin 5) :=
  PrimitiveAffineDegreeTwoPrimitiveSixteenRows18And19Complements.cycle_even

theorem a_ne_one : a ≠ 1 := by
  intro h
  have hh := congrArg (fun p : Source => p 0) h
  change (1 : Fin 5) = 0 at hh
  exact (by decide : (1 : Fin 5) ≠ 0) hh

theorem alternating_generators :
    Subgroup.closure ({a, second15} : Set Source) = alternatingGroup (Fin 5) := by
  have hsmall : Subgroup.closure ({a, commutator} : Set Source) =
      alternatingGroup (Fin 5) :=
    involutionCommutatorClosure_eq_alternating (by norm_num) a t (Equiv.swap_inv _ _)
      PrimitiveAffineDegreeTwoPrimitiveSixteenRows18And19Complements.symmetric_generators
      a_even a_ne_one
  have hc : commutator ∈ alternatingGroup (Fin 5) := by
    rw [← hsmall]
    exact Subgroup.subset_closure (by simp)
  let H := Subgroup.closure ({a, second15} : Set Source)
  have ha : a ∈ H := Subgroup.subset_closure (by simp)
  have hs : second15 ∈ H := Subgroup.subset_closure (by simp)
  have hu : commutator ∈ H := by
    have hword := H.mul_mem (H.mul_mem (H.inv_mem (H.pow_mem ha 3)) hs) (H.pow_mem ha 3)
    simpa [second15, mul_assoc] using hword
  apply le_antisymm
  · apply (Subgroup.closure_le _).mpr
    intro p hp
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hp
    rcases hp with rfl | rfl
    · exact a_even
    · exact (alternatingGroup (Fin 5)).mul_mem
        ((alternatingGroup (Fin 5)).mul_mem ((alternatingGroup (Fin 5)).pow_mem a_even 3) hc)
        ((alternatingGroup (Fin 5)).inv_mem ((alternatingGroup (Fin 5)).pow_mem a_even 3))
  · rw [← hsmall]
    apply (Subgroup.closure_le _).mpr
    intro p hp
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hp
    rcases hp with rfl | rfl
    · exact ha
    · exact hu

end FivePointSixConfigurationAction
end SymmetricSubgroupAsymptotics

end
