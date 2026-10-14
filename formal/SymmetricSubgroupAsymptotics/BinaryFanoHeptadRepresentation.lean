import SymmetricSubgroupAsymptotics.BinaryFanoHeptadGenerators
import SymmetricSubgroupAsymptotics.InvariantEmbeddingGroupHom

/-! The explicit heptad action lifts to the actual binary linear group.
The source is A8, with A7 included by fixing label7. The target homomorphism
is determined by the injective configuration chart and the faithful
four-bit permutation action. -/

set_option autoImplicit false
noncomputable section
open scoped Classical

namespace SymmetricSubgroupAsymptotics
namespace BinaryFanoHeptadRepresentation

open BinaryFourAffineImage BinaryFanoHeptadData BinaryFanoHeptadGenerators

theorem linearPerm_injective : Function.Injective linearPerm := by
  intro r s h
  apply LinearEquiv.ext
  intro v
  apply pointEquiv.injective
  have hv := congrArg (fun p : Equiv.Perm (Fin 16) => p (pointEquiv v)) h
  change pointEquiv (r (pointEquiv.symm (pointEquiv v))) =
    pointEquiv (s (pointEquiv.symm (pointEquiv v))) at hv
  simpa only [Equiv.symm_apply_apply] using hv

abbrev sourceAction : Source8 →* Equiv.Perm Heptad :=
  heptadAction.comp (alternatingGroup (Fin 8)).subtype

theorem all_liftable (g : Source8) :
    g ∈ InvariantEmbeddingGroupHom.liftable sourceAction configuration linearPerm := by
  have hle : (⊤ : Subgroup Source8) ≤
      InvariantEmbeddingGroupHom.liftable sourceAction configuration linearPerm := by
    rw [← source8_generators]
    apply (Subgroup.closure_le _).mpr
    intro p hp
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hp
    rcases hp with rfl | rfl
    · exact ⟨b20, beta_configuration⟩
    · exact ⟨gammaLinear, gamma_configuration⟩
  exact hle (Subgroup.mem_top g)

def hom8 : Source8 →* LinearGroup :=
  InvariantEmbeddingGroupHom.lift sourceAction configuration linearPerm
    configuration_injective linearPerm_injective all_liftable

theorem hom8_b8 : hom8 b8 = b20 :=
  InvariantEmbeddingGroupHom.lift_eq sourceAction configuration linearPerm
    configuration_injective linearPerm_injective all_liftable b8 b20 beta_configuration

theorem hom8_c8 : hom8 c8 = gammaLinear :=
  InvariantEmbeddingGroupHom.lift_eq sourceAction configuration linearPerm
    configuration_injective linearPerm_injective all_liftable c8 gammaLinear gamma_configuration

theorem hom8_a8 : hom8 a8 = a20 :=
  InvariantEmbeddingGroupHom.lift_eq sourceAction configuration linearPerm
    configuration_injective linearPerm_injective all_liftable a8 a20 alpha_configuration

def hom7 : Source7 →* LinearGroup := hom8.comp include7

theorem hom7_b7 : hom7 b7 = b20 := by
  change hom8 (include7 b7) = b20
  rw [include7_b7, hom8_b8]

theorem hom7_a7 : hom7 a7 = a20 := by
  change hom8 (include7 a7) = a20
  rw [include7_a7, hom8_a8]

/-- The same A8 action in the original row11 binary coordinates. -/
def hom11 : Source8 →* LinearGroup := (MulAut.conj chart11).toMonoidHom.comp hom8

theorem hom11_b8 : hom11 b8 = a11 := by
  change chart11 * hom8 b8 * chart11⁻¹ = a11
  rw [hom8_b8, chart11_beta]

theorem hom11_c8 : hom11 c8 = b11 := by
  change chart11 * hom8 c8 * chart11⁻¹ = b11
  rw [hom8_c8, chart11_gamma]

end BinaryFanoHeptadRepresentation
end SymmetricSubgroupAsymptotics

end
