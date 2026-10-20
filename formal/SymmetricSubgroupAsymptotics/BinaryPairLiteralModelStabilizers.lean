import SymmetricSubgroupAsymptotics.BinaryPairDegreeEightAxisModels
import SymmetricSubgroupAsymptotics.BinaryPairIntersectionRadicalStabilizer
import SymmetricSubgroupAsymptotics.BinaryNaturalEightPointStabilizer8T3State45
import SymmetricSubgroupAsymptotics.BinaryNaturalEightPointStabilizer8T3State46
import SymmetricSubgroupAsymptotics.BinaryNaturalEightPointStabilizer8T22State12
import SymmetricSubgroupAsymptotics.BinaryNaturalEightPointStabilizer8T22State13
import SymmetricSubgroupAsymptotics.BinaryNaturalEightPointStabilizer8T22State14

/-! The five finite stabilizer certificates apply to the original normal
subgroup after literal point-label conjugacy. Only the top subgroup type
is transported; all original kernel vectors and radicals remain fixed. -/
set_option autoImplicit false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics.BinaryPairFrame

variable {X : Type} {w : ℕ} {U : Subgroup (Equiv.Perm X)}
  (F : BinaryPairFrame U (Fin w)) (N : Subgroup U) [N.Normal]

theorem ambientAxis_inf_kernel : F.ambientAxis (N ⊓ F.top.ker) = F.ambientAxis N := by
  apply (F.ambientAxis_eq_iff _ _).mpr
  ext u
  simp only [Subgroup.mem_inf]
  tauto

theorem kernel_le_normal_of_literal_model_stabilizers [Finite X]
    (H : Subgroup (Equiv.Perm (Fin w))) (hH : F.top.range = H)
    {r : ℕ} (row : Fin r → H) (hrow : Function.Bijective row)
    (A R : Submodule (ZMod 2) (Fin w → ZMod 2)) (cap : ℕ)
    (hcount : ∀ v, v ∉ A → Nat.card {i : Fin r //
      ((binaryPermutationRepresentation w).comp H.subtype) (row i) v - v ∈ R} ≤ cap)
    (haxis : F.ambientAxis N = A)
    (hrad : F.ambientAxis (primeRelativeRadical 2 (N ⊓ F.top.ker)) = R)
    (hlarge : cap < Nat.card (N.map F.top.rangeRestrict))
    (heq : Module.finrank (ZMod 2) (primeRelativeCharacters 2 N) =
      Module.finrank (ZMod 2) (primeRelativeCharacters 2 (N ⊓ F.top.ker)) +
        Module.finrank (ZMod 2)
          (primeRelativeCharacters 2 (normalChainQuotient (N ⊓ F.top.ker) N))) :
    F.top.ker ≤ N := by
  let e : F.top.range ≃* H := MulEquiv.subgroupCongr hH
  apply F.kernel_le_normal_of_small_radical_stabilizers N
    (fun i => e.symm (row i)) (e.symm.bijective.comp hrow) cap _ hlarge heq
  intro v hv
  rw [haxis] at hv
  rw [hrad]
  exact hcount v hv

end SymmetricSubgroupAsymptotics.BinaryPairFrame

namespace SymmetricSubgroupAsymptotics.BinaryPairFrame

variable {X : Type} [Finite X] {U : Subgroup (Equiv.Perm X)}
  (F : BinaryPairFrame U (Fin 8)) (hU : IsPGroup 2 U)
  (N : Subgroup U) [N.Normal]

include hU

theorem regular_kernel_le_normal_of_head_equality
    (hH : F.top.range = Subgroup.closure (Set.range BinaryMenuCayley8T3.generators))
    (hB : 2 < MarkedC4.normalGen (N ⊓ F.top.ker))
    (hlarge : 2 < Nat.card (N.map F.top.rangeRestrict))
    (heq : Module.finrank (ZMod 2) (primeRelativeCharacters 2 N) =
      Module.finrank (ZMod 2) (primeRelativeCharacters 2 (N ⊓ F.top.ker)) +
        Module.finrank (ZMod 2)
          (primeRelativeCharacters 2 (normalChainQuotient (N ⊓ F.top.ker) N))) :
    F.top.ker ≤ N := by
  rcases F.regular_large_axis_models hU (N ⊓ F.top.ker) inf_le_right hH hB with
    ⟨hA, hR⟩ | ⟨hA, hR⟩
  · exact F.kernel_le_normal_of_literal_model_stabilizers N
      BinaryEightOriginalRowActions.regularH hH
      BinaryEightOriginalRowActions.regularRow BinaryEightOriginalRowActions.regularRow_bijective
      _ _ 2 BinaryNaturalEightPointStabilizer8T3State45.count_bound
      ((F.ambientAxis_inf_kernel N).symm.trans hA) hR hlarge heq
  · exact F.kernel_le_normal_of_literal_model_stabilizers N
      BinaryEightOriginalRowActions.regularH hH
      BinaryEightOriginalRowActions.regularRow BinaryEightOriginalRowActions.regularRow_bijective
      _ _ 2 BinaryNaturalEightPointStabilizer8T3State46.count_bound
      ((F.ambientAxis_inf_kernel N).symm.trans hA) hR hlarge heq

theorem heisenberg_kernel_le_normal_of_head_equality
    (hH : F.top.range = Subgroup.closure (Set.range BinaryMenuCayley8T22.generators))
    (hB : 1 < MarkedC4.normalGen (N ⊓ F.top.ker))
    (hlarge : 8 < Nat.card (N.map F.top.rangeRestrict))
    (heq : Module.finrank (ZMod 2) (primeRelativeCharacters 2 N) =
      Module.finrank (ZMod 2) (primeRelativeCharacters 2 (N ⊓ F.top.ker)) +
        Module.finrank (ZMod 2)
          (primeRelativeCharacters 2 (normalChainQuotient (N ⊓ F.top.ker) N))) :
    F.top.ker ≤ N := by
  rcases F.heisenberg_large_axis_models hU (N ⊓ F.top.ker) inf_le_right hH hB with
    ⟨hA, hR⟩ | ⟨hA, hR⟩ | ⟨hA, hR⟩
  · exact F.kernel_le_normal_of_literal_model_stabilizers N
      BinaryEightOriginalRowActions.heisenbergH hH
      BinaryEightOriginalRowActions.heisenbergRow BinaryEightOriginalRowActions.heisenbergRow_bijective
      _ _ 8 BinaryNaturalEightPointStabilizer8T22State12.count_bound
      ((F.ambientAxis_inf_kernel N).symm.trans hA) hR hlarge heq
  · exact F.kernel_le_normal_of_literal_model_stabilizers N
      BinaryEightOriginalRowActions.heisenbergH hH
      BinaryEightOriginalRowActions.heisenbergRow BinaryEightOriginalRowActions.heisenbergRow_bijective
      _ _ 8 BinaryNaturalEightPointStabilizer8T22State13.count_bound
      ((F.ambientAxis_inf_kernel N).symm.trans hA) hR hlarge heq
  · exact F.kernel_le_normal_of_literal_model_stabilizers N
      BinaryEightOriginalRowActions.heisenbergH hH
      BinaryEightOriginalRowActions.heisenbergRow BinaryEightOriginalRowActions.heisenbergRow_bijective
      _ _ 8 BinaryNaturalEightPointStabilizer8T22State14.count_bound
      ((F.ambientAxis_inf_kernel N).symm.trans hA) hR hlarge heq

end SymmetricSubgroupAsymptotics.BinaryPairFrame
