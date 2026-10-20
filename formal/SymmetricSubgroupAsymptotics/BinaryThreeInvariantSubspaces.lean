import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
import Mathlib.LinearAlgebra.Span.Basic
import Mathlib.Data.ZMod.Basic

/-! Small analytic witnesses separating fixed vectors and fixed dual
vectors from irreducibility in dimension three over F2. The finite checks
quantify only over the eight vectors, not over any group or subgroup. -/

set_option autoImplicit false
open scoped Matrix

namespace SymmetricSubgroupAsymptotics.BinaryThreeInvariantSubspaces

abbrev Vector := Fin 3 → ZMod 2
abbrev Ambient := Matrix.GeneralLinearGroup (Fin 3) (ZMod 2)

private theorem outside_line : ∀ v : Vector,
    ∃ w : Vector, ∀ c : ZMod 2, c • v ≠ w := by decide +kernel

theorem line (v : Vector) (hv : v ≠ 0) :
    ∃ W : Submodule (ZMod 2) Vector, W ≠ ⊥ ∧ W ≠ ⊤ ∧
      ∀ g : Ambient, g.val *ᵥ v = v → ∀ w ∈ W, g.val *ᵥ w ∈ W := by
  let W : Submodule (ZMod 2) Vector := Submodule.span (ZMod 2) {v}
  refine ⟨W, ?_, ?_, ?_⟩
  · intro h
    have hmem : v ∈ W := Submodule.mem_span_singleton_self v
    rw [h] at hmem
    exact hv ((Submodule.mem_bot (R := ZMod 2)).mp hmem)
  · obtain ⟨w, hw⟩ := outside_line v
    intro h
    have hmem : w ∈ W := by rw [h]; exact Submodule.mem_top
    obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp hmem
    exact hw c hc
  · intro g hg w hw
    obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp hw
    rw [Matrix.mulVec_smul, hg]
    exact W.smul_mem c (Submodule.mem_span_singleton_self v)

private def kernel (l : Vector) : Submodule (ZMod 2) Vector where
  carrier := {v | l ⬝ᵥ v = 0}
  zero_mem' := by simp
  add_mem' := by
    intro v w hv hw
    change l ⬝ᵥ (v + w) = 0
    rw [dotProduct_add, hv, hw, add_zero]
  smul_mem' := by
    intro c v hv
    change l ⬝ᵥ (c • v) = 0
    rw [dotProduct_smul, hv, smul_zero]

private theorem kernel_witnesses : ∀ l : Vector, l ≠ 0 →
    (∃ v : Vector, v ≠ 0 ∧ l ⬝ᵥ v = 0) ∧
      ∃ w : Vector, l ⬝ᵥ w ≠ 0 := by decide +kernel

theorem plane (l : Vector) (hl : l ≠ 0) :
    ∃ W : Submodule (ZMod 2) Vector, W ≠ ⊥ ∧ W ≠ ⊤ ∧
      ∀ g : Ambient, l ᵥ* g.val = l → ∀ w ∈ W, g.val *ᵥ w ∈ W := by
  obtain ⟨⟨v, hv, hlv⟩, w, hlw⟩ := kernel_witnesses l hl
  refine ⟨kernel l, ?_, ?_, ?_⟩
  · intro h
    have hmem : v ∈ kernel l := hlv
    rw [h] at hmem
    exact hv ((Submodule.mem_bot (R := ZMod 2)).mp hmem)
  · intro h
    have hmem : w ∈ kernel l := by rw [h]; exact Submodule.mem_top
    exact hlw hmem
  · intro g hg z hz
    change l ⬝ᵥ (g.val *ᵥ z) = 0
    rw [Matrix.dotProduct_mulVec, hg]
    exact hz

end SymmetricSubgroupAsymptotics.BinaryThreeInvariantSubspaces
