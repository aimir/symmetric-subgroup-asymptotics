import SymmetricSubgroupAsymptotics.LinearJointAnnihilator

/-! Uniform joint-annihilator bounds from independent parameter tuples.
Every retained parameter annihilates the same original subspace W, so
an independent retained tuple puts W in its actual common kernel. No
enumeration of W or replacement of the original family is involved. -/
set_option autoImplicit false
noncomputable section

namespace SymmetricSubgroupAsymptotics

variable {k L V U : Type*} [Field k]
    [AddCommGroup L] [Module k L]
    [AddCommGroup V] [Module k V]
    [AddCommGroup U] [Module k U]

/-- An arbitrary tuple of retained parameters annihilates the whole
original W simultaneously. Independence is not needed for this inclusion. -/
theorem le_iInf_ker_of_mem_linearJointAnnihilator {ι : Type*}
    (F : L →ₗ[k] (V →ₗ[k] U)) (W : Submodule k V) (v : ι → L)
    (hv : ∀ i, v i ∈ linearJointAnnihilator F W) :
    W ≤ ⨅ i, (F (v i)).ker :=
  le_iInf (fun i => (mem_linearJointAnnihilator_iff_le_ker F W (v i)).mp (hv i))

/-- If every independent (q+1)-tuple has common kernel dimension at most
a, a larger original subspace can retain at most q parameter dimensions. -/
theorem linearJointAnnihilator_finrank_le_of_common_kernel_bound
    [FiniteDimensional k L] [FiniteDimensional k V]
    (F : L →ₗ[k] (V →ₗ[k] U)) (W : Submodule k V) (q a : ℕ)
    (hcommon : ∀ v : Fin (q+1) → L, LinearIndependent k v →
      Module.finrank k ↥(⨅ i, (F (v i)).ker) ≤ a)
    (hW : a < Module.finrank k W) :
    Module.finrank k (linearJointAnnihilator F W) ≤ q := by
  classical
  let J := linearJointAnnihilator F W
  by_contra h
  have hlarge : q+1 ≤ Module.finrank k J :=
    Nat.succ_le_of_lt (lt_of_not_ge h)
  obtain ⟨v,hv⟩ := exists_linearIndependent_of_le_finrank hlarge
  have hi : LinearIndependent k (fun i : Fin (q+1) => (v i : L)) :=
    hv.map' J.subtype J.ker_subtype
  have hle : W ≤ ⨅ i : Fin (q+1), (F (v i : L)).ker :=
    le_iInf_ker_of_mem_linearJointAnnihilator F W
      (fun i : Fin (q+1) => (v i : L)) (fun i => (v i).2)
  exact (not_le_of_gt hW)
    ((Submodule.finrank_mono hle).trans (hcommon _ hi))

/-- A zero common kernel bounds retained dimensions for any nonzero W.
The original input space need not be finite dimensional in this version. -/
theorem linearJointAnnihilator_finrank_le_of_common_kernel_eq_bot
    [FiniteDimensional k L]
    (F : L →ₗ[k] (V →ₗ[k] U)) (W : Submodule k V) (q : ℕ)
    (hcommon : ∀ v : Fin (q+1) → L, LinearIndependent k v →
      (⨅ i, (F (v i)).ker) = ⊥)
    (hW : W ≠ ⊥) :
    Module.finrank k (linearJointAnnihilator F W) ≤ q := by
  classical
  let J := linearJointAnnihilator F W
  by_contra h
  have hlarge : q+1 ≤ Module.finrank k J :=
    Nat.succ_le_of_lt (lt_of_not_ge h)
  obtain ⟨v,hv⟩ := exists_linearIndependent_of_le_finrank hlarge
  have hi : LinearIndependent k (fun i : Fin (q+1) => (v i : L)) :=
    hv.map' J.subtype J.ker_subtype
  have hle : W ≤ ⨅ i : Fin (q+1), (F (v i : L)).ker :=
    le_iInf_ker_of_mem_linearJointAnnihilator F W
      (fun i : Fin (q+1) => (v i : L)) (fun i => (v i).2)
  exact hW (le_antisymm (hle.trans (hcommon _ hi).le) bot_le)

end SymmetricSubgroupAsymptotics
