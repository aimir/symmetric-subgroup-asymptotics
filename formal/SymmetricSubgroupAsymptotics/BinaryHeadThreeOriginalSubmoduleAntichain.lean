import SymmetricSubgroupAsymptotics.BinaryHeadThreeActualLeadingAntichain
import SymmetricSubgroupAsymptotics.BinaryPairPolynomialExtraShear

/-! The leading antichain belongs to the same original invariant
subspace. All translation and extra-shear operators are actual group
members, acting in its original coordinates. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped Classical MonoidAlgebra
namespace SymmetricSubgroupAsymptotics
open BinaryBooleanFourPolynomialCoordinates BinaryRegular46HeadThreeMonomial
local instance : Fact (Nat.Prime 2) := ⟨by decide⟩
variable {G : Type} [Group G] [MulAction G (Fin 16)]

set_option maxHeartbeats 2000000 in
theorem binary_head_three_original_submodule_antichain
    (W : Subrepresentation (permutationFunctionRepresentation (ZMod 2) G (Fin 16)))
    (e : Equiv.Perm (Fin 16))
    (htranslations : ∀ i : Fin 4, ∃ g : G,
      ∀ j, g⁻¹ • e.symm j = e.symm (flipIndex i j))
    (hextra : ∃ g : G, ∀ j, g⁻¹ • e.symm j =
      e.symm (BinaryCommonEightExtraShearLeading.booleanPermutation.symm j))
    (hhead : 3 ≤ Module.finrank (ZMod 2)
      (W.toRepresentation.IntertwiningMap
        (Representation.trivial (ZMod 2) G (ZMod 2)))) :
    ∃ (S : Finset W.toRepresentation.asModule)
      (label : W.toRepresentation.asModule → Fin 16),
      Submodule.span (ZMod 2)[G] (S : Set W.toRepresentation.asModule) = ⊤ ∧
      (∀ v ∈ S, FiniteRowLeadingWeight.HasLeading
        (evaluate (fun j => (W.toRepresentation.asModuleEquiv v).val (e.symm j))) (label v)) ∧
      Set.InjOn label (S : Set W.toRepresentation.asModule) ∧
      IsAntichain TopRel (S.image label : Set (Fin 16)) ∧
      3 ≤ (S.image label).card := by
  let P : V ≃ₗ[ZMod 2] V :=
    (BinaryBooleanFourPolynomialCoordinates.reindex e).trans coordinates
  let C : W.toSubmodule →ₗ[ZMod 2] V := P.toLinearMap.comp W.toSubmodule.subtype
  have hC : Function.Injective C := by
    intro a b hab
    apply Subtype.ext
    apply P.injective
    change P a.val = P b.val at hab
    exact hab
  have hdiff (i : Fin 4) : ∃ g : G, ∀ v : W.toSubmodule,
      C (W.toRepresentation g v - v) = derivative i (C v) := by
    obtain ⟨g, hg⟩ := htranslations i
    refine ⟨g, ?_⟩
    intro v
    change evaluate (fun j => (v.val (g⁻¹ • e.symm j) - v.val (e.symm j))) =
      derivative i (evaluate (fun j => v.val (e.symm j)))
    rw [derivative_evaluate]
    congr 1
    funext j
    rw [hg]
    rfl
  have hexdiff : ∃ g : G, ∀ v : W.toSubmodule,
      C (W.toRepresentation g v - v) =
        BinaryCommonEightExtraShearLeading.operator (C v) := by
    obtain ⟨g, hg⟩ := hextra
    refine ⟨g, ?_⟩
    intro v
    rw [← permutationDifference_extraShear]
    change evaluate (fun j => (v.val (g⁻¹ • e.symm j) - v.val (e.symm j))) =
      permutationDifference BinaryCommonEightExtraShearLeading.booleanPermutation
        (evaluate (fun j => v.val (e.symm j)))
    rw [permutationDifference_evaluate]
    congr 1
    funext j
    rw [hg]
    rfl
  exact binary_head_three_actual_leading_antichain W.toRepresentation C hC hdiff hexdiff hhead

end SymmetricSubgroupAsymptotics
