import SymmetricSubgroupAsymptotics.BinaryHeadThreeOriginalSubmoduleAntichain
import SymmetricSubgroupAsymptotics.BinaryHeadThreeAntichainCoverage

/-! The sparse three-label certificate is supplied by actual vectors
of the original invariant subspace, including every lower polynomial term. -/
set_option autoImplicit false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics
open BinaryBooleanFourPolynomialCoordinates BinaryRegular46HeadThreeMonomial
local instance : Fact (Nat.Prime 2) := ⟨by decide⟩
variable {G : Type} [Group G] [MulAction G (Fin 16)]

theorem binary_head_three_original_leading_shears
    (W : Subrepresentation (permutationFunctionRepresentation (ZMod 2) G (Fin 16)))
    (e : Equiv.Perm (Fin 16))
    (htranslations : ∀ i : Fin 4, ∃ g : G,
      ∀ j, g⁻¹ • e.symm j = e.symm (flipIndex i j))
    (hextra : ∃ g : G, ∀ j, g⁻¹ • e.symm j =
      e.symm (BinaryCommonEightExtraShearLeading.booleanPermutation.symm j))
    (hhead : 3 ≤ Module.finrank (ZMod 2)
      (W.toRepresentation.IntertwiningMap
        (Representation.trivial (ZMod 2) G (ZMod 2)))) :
    ∃ c : Fin 36, ∀ k : Fin 3, ∃ a : V,
      FiniteRowLeadingWeight.HasLeading a (labels c k) ∧
      (fun x => evaluate a (e x)) ∈ W.toSubmodule := by
  obtain ⟨S, label, _, hlead, _, hanti, hcard⟩ :=
    binary_head_three_original_submodule_antichain W e htranslations hextra hhead
  obtain ⟨c, hc⟩ := antichain_contains_labels (S.image label) hanti hcard
  refine ⟨c, ?_⟩
  intro k
  obtain ⟨v, hv, hlabel⟩ := Finset.mem_image.mp (hc k)
  let f : V := (W.toRepresentation.asModuleEquiv v).val
  let a : V := evaluate (fun j => f (e.symm j))
  refine ⟨a, ?_, ?_⟩
  · rw [← hlabel]
    exact hlead v hv
  · have he : (fun x => evaluate a (e x)) = f := by
      change (fun x => evaluate (evaluate (fun j => f (e.symm j))) (e x)) = f
      rw [evaluate_involutive]
      funext x
      rw [Equiv.symm_apply_apply]
    rw [he]
    exact (W.toRepresentation.asModuleEquiv v).property

end SymmetricSubgroupAsymptotics
