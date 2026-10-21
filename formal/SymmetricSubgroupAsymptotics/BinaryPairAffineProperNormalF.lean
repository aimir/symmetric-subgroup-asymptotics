import SymmetricSubgroupAsymptotics.BinaryPairAmbientAffineEmbedding
import SymmetricSubgroupAsymptotics.BinaryPairDerivedZeroLifts

/-! A proper normal-F template inside the SAME original affine action.
The selected zero lift is obtained from its actual affine class, while
all other original lifts may have arbitrary offsets. -/
set_option autoImplicit false
noncomputable section
open scoped commutatorElement
namespace SymmetricSubgroupAsymptotics.BinaryPairFrame
open SemidirectProduct LinearSemidirectCoprimeSocleBounds
local instance affineProperNormalF_primeTwo : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
variable {X : Type} {w : ℕ} {U : Subgroup (Equiv.Perm X)}
    (F : BinaryPairFrame U (Fin w))

def affineProperNormalF (B : Submodule (ZMod 2) (Fin w → ZMod 2))
    (z : F.top.range) : Subgroup U :=
  (properNormalF F.ambientAffineLinearAction B z).comap F.ambientAffineEmbedding

/-- Every displayed template generator is an actual original element;
therefore pulling back the ambient template does not shrink it. -/
theorem affineProperNormalF_map (B : Submodule (ZMod 2) (Fin w → ZMod 2))
    (z : F.top.range) (hB : B ≤ F.kernelSpace) (hz : F.affineClass z = 0) :
    (F.affineProperNormalF B z).map F.ambientAffineEmbedding =
      properNormalF F.ambientAffineLinearAction B z := by
  have hr : properNormalF F.ambientAffineLinearAction B z ≤
      F.ambientAffineEmbedding.range := by
    apply (Subgroup.closure_le _).mpr
    rintro _ ⟨i,rfl⟩
    cases i with
    | inl b =>
      obtain ⟨k,hk⟩ := hB b.property
      change F.bits k.toMul = b.val at hk
      refine ⟨k.toMul.val,?_⟩
      rw [F.ambientAffineEmbedding_kernel,hk]
      rfl
    | inr _ =>
      obtain ⟨u,ht,ha⟩ := (F.affine_graph_fibre z 0).mpr (by rw [map_zero,hz])
      refine ⟨u,?_⟩
      apply SemidirectProduct.ext
      · exact congrArg Multiplicative.ofAdd ha
      · exact ht
  apply le_antisymm
  · rintro _ ⟨u,hu,rfl⟩
    exact hu
  · intro y hy
    obtain ⟨u,hu⟩ := hr hy
    refine ⟨u,?_,hu⟩
    change F.ambientAffineEmbedding u ∈ properNormalF F.ambientAffineLinearAction B z
    rw [hu]
    exact hy

theorem affineProperNormalF_normal
    (B C : Submodule (ZMod 2) (Fin w → ZMod 2)) (z : F.top.range)
    (hCB : C ≤ B) (hz : z ∈ Subgroup.center F.top.range)
    (hC : ∀ r v, v ∈ C → F.ambientAffineLinearAction r v ∈ C)
    (hBdisp : ∀ r v, v ∈ B → F.ambientAffineLinearAction r v-v ∈ C)
    (hzdisp : ∀ v, F.ambientAffineLinearAction z v-v ∈ C) :
    (F.affineProperNormalF B z).Normal := by
  letI : (properNormalF F.ambientAffineLinearAction B z).Normal :=
    properNormalF_normal F.ambientAffineLinearAction B C z hCB hz hC hBdisp hzdisp
  exact Subgroup.Normal.comap inferInstance F.ambientAffineEmbedding

/-- The mixed commutator stays in the original physical coordinate
subgroup. This statement holds before any normal quotient is chosen. -/
theorem affineProperNormalF_mixedCommutator_le
    (B C : Submodule (ZMod 2) (Fin w → ZMod 2)) (z : F.top.range)
    (hz : z ∈ Subgroup.center F.top.range)
    (hC : ∀ r v, v ∈ C → F.ambientAffineLinearAction r v ∈ C)
    (hBdisp : ∀ r v, v ∈ B → F.ambientAffineLinearAction r v-v ∈ C)
    (hzdisp : ∀ v, F.ambientAffineLinearAction z v-v ∈ C) :
    ⁅F.affineProperNormalF B z,(⊤ : Subgroup U)⁆ ≤ F.coordinateSubgroup C := by
  rw [← F.ambientAffine_translation_preimage]
  apply (Subgroup.map_le_iff_le_comap).mp
  rw [Subgroup.map_commutator]
  have hp : (F.affineProperNormalF B z).map F.ambientAffineEmbedding ≤
      properNormalF F.ambientAffineLinearAction B z := by
    rintro _ ⟨u,hu,rfl⟩
    exact hu
  exact (Subgroup.commutator_mono hp le_top).trans
    (properNormalF_mixedCommutator_le F.ambientAffineLinearAction B C z hz hC hBdisp hzdisp)

end SymmetricSubgroupAsymptotics.BinaryPairFrame
