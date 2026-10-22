import SymmetricSubgroupAsymptotics.CFSGSerreGeneratorRelations

/-! A linear subspace containing the actual E/F generators and stable
under their actual adjoints is the entire original rational quotient.
This is a generation argument, not a dimension or basis assumption. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section

namespace SymmetricSubgroupAsymptotics.CFSGSerreGeneratedInvariantSpan
open CFSG.Models.Chevalley CFSGSerreLocalNilpotence
variable {n : ℕ} (A : Matrix (Fin n) (Fin n) ℤ)

def adStabilizer (W : Submodule ℚ (RationalLie A)) : LieSubalgebra ℚ (RationalLie A) where
  carrier := {x | ∀ y ∈ W, ⁅x, y⁆ ∈ W}
  zero_mem' := by intro y hy; rw [zero_lie]; exact W.zero_mem
  add_mem' := by
    intro x y hx hy z hz
    rw [add_lie]
    exact W.add_mem (hx z hz) (hy z hz)
  smul_mem' := by
    intro a x hx z hz
    rw [smul_lie]
    exact W.smul_mem a (hx z hz)
  lie_mem' := by
    intro x y hx hy z hz
    rw [lie_lie]
    exact W.sub_mem (hx _ (hy z hz)) (hy _ (hx z hz))

theorem eq_top_of_EF_stable (W : Submodule ℚ (RationalLie A))
    (hE : ∀ i, generator A (.E i) ∈ W) (hF : ∀ i, generator A (.F i) ∈ W)
    (hEstable : ∀ i, ∀ y ∈ W, ⁅generator A (.E i), y⁆ ∈ W)
    (hFstable : ∀ i, ∀ y ∈ W, ⁅generator A (.F i), y⁆ ∈ W) : W = ⊤ := by
  have hS : adStabilizer A W = ⊤ := by
    apply top_unique
    rw [← generator_lieSpan_eq_top A]
    apply LieSubalgebra.lieSpan_le.mpr
    rintro x ⟨g, rfl⟩
    cases g with
    | E i => exact hEstable i
    | F i => exact hFstable i
    | H i =>
      rw [← generator_EF_same A i]
      exact (adStabilizer A W).lie_mem (hEstable i) (hFstable i)
  let T : LieSubalgebra ℚ (RationalLie A) :=
    { __ := W
      lie_mem' := by
        intro x y hx hy
        have hxs : x ∈ adStabilizer A W := by rw [hS]; trivial
        exact hxs y hy }
  have hT : T = ⊤ := by
    apply top_unique
    rw [← generator_lieSpan_eq_top A]
    apply LieSubalgebra.lieSpan_le.mpr
    rintro x ⟨g, rfl⟩
    cases g with
    | E i => exact hE i
    | F i => exact hF i
    | H i =>
      rw [← generator_EF_same A i]
      exact T.lie_mem (hE i) (hF i)
  exact congrArg LieSubalgebra.toSubmodule hT

end SymmetricSubgroupAsymptotics.CFSGSerreGeneratedInvariantSpan
