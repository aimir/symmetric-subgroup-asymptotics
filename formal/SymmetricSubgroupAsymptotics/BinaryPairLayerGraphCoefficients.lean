import SymmetricSubgroupAsymptotics.BinaryPairModuleLayerGraph
import SymmetricSubgroupAsymptotics.BinaryCoordinateSpaces

/-! Scalar coefficients describe every original graph section once its
actual pair-sum layer has a reversible chart. No enumeration of original
sixteen-dimensional subspaces is needed. -/
set_option autoImplicit false
noncomputable section
open scoped BigOperators
namespace SymmetricSubgroupAsymptotics.BinaryPairFrame

variable {X : Type} {w d : ℕ} {U : Subgroup (Equiv.Perm X)}
    (F : BinaryPairFrame U (Fin w))

/-- The same original module state is determined by one vector of scalar
coefficients on the retained pair-sum chart. -/
theorem exists_pairModule_graph_coefficients
    (W : Subrepresentation (permutationFunctionRepresentation (ZMod 2) U X))
    (C : BinaryCoordinateSpace w d)
    (hS : (F.pairSumModuleLayer W).toSubmodule = C.space)
    (ell : (Fin w → ZMod 2) →ₗ[ZMod 2] ZMod 2)
    (hL : (F.pairConstantModuleLayer W).toSubmodule = ell.ker) :
    ∃ c : Fin d → ZMod 2, ∀ f : X → ZMod 2, f ∈ W.toSubmodule ↔
      F.pairSum f ∈ C.space ∧ ell (F.pairZeroRestriction f) =
        ∑ i, (C.coordinates (F.pairSum f)) i * c i := by
  obtain ⟨phi, hphi⟩ := F.exists_pairModule_graph_of_constant_hyperplane W ell hL
  let inclusion : (Fin d → ZMod 2) →ₗ[ZMod 2]
      (F.pairSumModuleLayer W).toSubmodule := {
    toFun := fun v => ⟨C.inclusion v, by rw [hS]; exact ⟨v, rfl⟩⟩
    map_add' := fun v z => Subtype.ext (C.inclusion.map_add v z)
    map_smul' := fun c v => Subtype.ext (C.inclusion.map_smul c v) }
  let psi := phi.comp inclusion
  let c : Fin d → ZMod 2 := fun i => psi (Pi.single i 1)
  have hpsi (v : Fin d → ZMod 2) : psi v = ∑ i, v i * c i := by
    have hv : (∑ i, v i • Pi.single i (1 : ZMod 2)) = v := by
      ext j
      simp [Pi.single_apply, mul_ite]
    conv_lhs => rw [← hv, map_sum]
    apply Finset.sum_congr rfl
    intro i _
    rw [map_smul]
    rfl
  have hvalue (v : Fin w → ZMod 2)
      (hv : v ∈ (F.pairSumModuleLayer W).toSubmodule) :
      phi ⟨v, hv⟩ = ∑ i, (C.coordinates v) i * c i := by
    have hvC : v ∈ C.space := by rwa [← hS]
    have he : (⟨v, hv⟩ : (F.pairSumModuleLayer W).toSubmodule) =
        inclusion (C.coordinates v) := by
      apply Subtype.ext
      exact ((C.mem_iff v).mp hvC).symm
    rw [he]
    exact hpsi _
  refine ⟨c, ?_⟩
  intro f
  rw [hphi f]
  constructor
  · rintro ⟨hsum, he⟩
    refine ⟨by rwa [← hS], he.trans (hvalue _ hsum)⟩
  · rintro ⟨hsum, he⟩
    have hs : F.pairSum f ∈ (F.pairSumModuleLayer W).toSubmodule := by rwa [hS]
    exact ⟨hs, he.trans (hvalue _ hs).symm⟩

end SymmetricSubgroupAsymptotics.BinaryPairFrame
