import Mathlib.LinearAlgebra.FiniteDimensional.Basic

/-! Uniform joint-annihilator dimensions from actual single and pair
kernel bounds. A linear family F of maps defines the parameters vanishing
on an arbitrary subspace W. No enumeration of W is needed. For bilinear
forms, take the target U to be the dual of their original vector space;
alternation is not required by these purely linear implications. -/
set_option autoImplicit false
noncomputable section

namespace SymmetricSubgroupAsymptotics

variable {k L V U : Type*} [Field k]
    [AddCommGroup L] [Module k L]
    [AddCommGroup V] [Module k V]
    [AddCommGroup U] [Module k U]

/-- Parameters whose original linear map vanishes on every member of W. -/
def linearJointAnnihilator (F : L →ₗ[k] (V →ₗ[k] U)) (W : Submodule k V) :
    Submodule k L where
  carrier := {a | ∀ v ∈ W, F a v = 0}
  zero_mem' := by
    intro v _
    simp only [map_zero, LinearMap.zero_apply]
  add_mem' := by
    intro a b ha hb v hv
    simp only [map_add, LinearMap.add_apply, ha v hv, hb v hv, add_zero]
  smul_mem' := by
    intro c a ha v hv
    simp only [map_smul, LinearMap.smul_apply, ha v hv, smul_zero]

@[simp]
theorem mem_linearJointAnnihilator_iff
    (F : L →ₗ[k] (V →ₗ[k] U)) (W : Submodule k V) (a : L) :
    a ∈ linearJointAnnihilator F W ↔ ∀ v ∈ W, F a v = 0 := Iff.rfl

theorem mem_linearJointAnnihilator_iff_le_ker
    (F : L →ₗ[k] (V →ₗ[k] U)) (W : Submodule k V) (a : L) :
    a ∈ linearJointAnnihilator F W ↔ W ≤ (F a).ker := Iff.rfl

/-- Two independent retained parameters would force the whole original
W into their common kernel. Thus a nonzero W retains at most one dimension
when every independent pair of actual maps has zero common kernel. -/
theorem linearJointAnnihilator_finrank_le_one [FiniteDimensional k L]
    (F : L →ₗ[k] (V →ₗ[k] U)) (W : Submodule k V)
    (hpair : ∀ v : Fin 2 → L, LinearIndependent k v →
      (F (v 0)).ker ⊓ (F (v 1)).ker = ⊥)
    (hW : W ≠ ⊥) :
    Module.finrank k (linearJointAnnihilator F W) ≤ 1 := by
  classical
  let J := linearJointAnnihilator F W
  by_contra h
  have htwo : 2 ≤ Module.finrank k J := Nat.succ_le_of_lt (lt_of_not_ge h)
  obtain ⟨v,hv⟩ := exists_linearIndependent_of_le_finrank htwo
  have hi : LinearIndependent k (fun i : Fin 2 => (v i : L)) :=
    hv.map' J.subtype J.ker_subtype
  have hzero := hpair (fun i : Fin 2 => (v i : L)) hi
  have hle : W ≤ (F (v 0 : L)).ker ⊓ (F (v 1 : L)).ker := by
    intro w hw
    exact ⟨(v 0).2 w hw, (v 1).2 w hw⟩
  exact hW (le_antisymm (hle.trans hzero.le) bot_le)

/-- If every nonzero parameter's actual kernel has dimension at most a,
then a larger W retains only zero. This does not require the pair premise. -/
theorem linearJointAnnihilator_eq_bot_of_radical_bounds [FiniteDimensional k V]
    (F : L →ₗ[k] (V →ₗ[k] U)) (W : Submodule k V) (a : ℕ)
    (hsingle : ∀ l : L, l ≠ 0 → Module.finrank k (F l).ker ≤ a)
    (hW : a < Module.finrank k W) :
    linearJointAnnihilator F W = ⊥ := by
  classical
  apply le_antisymm _ bot_le
  intro l hl
  change l = 0
  by_contra hnonzero
  have hle : W ≤ (F l).ker := fun w hw => hl w hw
  exact (not_le_of_gt hW)
    ((Submodule.finrank_mono hle).trans (hsingle l hnonzero))

theorem linearJointAnnihilator_finrank_eq_zero_of_radical_bounds
    [FiniteDimensional k V]
    (F : L →ₗ[k] (V →ₗ[k] U)) (W : Submodule k V) (a : ℕ)
    (hsingle : ∀ l : L, l ≠ 0 → Module.finrank k (F l).ker ≤ a)
    (hW : a < Module.finrank k W) :
    Module.finrank k (linearJointAnnihilator F W) = 0 := by
  rw [linearJointAnnihilator_eq_bot_of_radical_bounds F W a hsingle hW]
  exact finrank_bot k L

end SymmetricSubgroupAsymptotics
