import SymmetricSubgroupAsymptotics.CFSGOrthogonalBSingularPlaneOrbit
import Mathlib.LinearAlgebra.LinearIndependent.Lemmas
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.Tactic.FinCases

/-! Exact natural label coverage: the conjugate long-root planes are
precisely the original totally singular submodules of dimension two.
Both directions preserve the SAME original natural submodule. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Matrix
namespace SymmetricSubgroupAsymptotics.CFSGOrthogonalBUnipotent
open CFSGOrthogonalBSerreMatrices
variable {K : Type} [Field K]

theorem standardRootPlane_finrank (s : ℕ) :
    Module.finrank K (standardRootPlane (K := K) s) = 2 := by
  let u := positiveVector (K := K) s 0
  let v := positiveVector (K := K) s (secondIndex s)
  have hu : u ≠ 0 := by
    intro hz
    have he := congrFun hz (pos (s + 3) 0)
    simp [u, positiveVector] at he
  have hnot (a : K) : a • u ≠ v := by
    intro hz
    have he := congrFun hz (pos (s + 3) (secondIndex s))
    simp [u, v, positiveVector, pos, secondIndex] at he
  have hi : LinearIndependent K ![u, v] := (LinearIndependent.pair_iff' hu).mpr hnot
  have hr : Set.range ![u, v] = ({u, v} : Set (Index (s + 3) → K)) := by
    ext x
    constructor
    · rintro ⟨i, rfl⟩
      fin_cases i <;> simp
    · rintro (hx | hx)
      · exact ⟨0, hx.symm⟩
      · exact ⟨1, (Set.mem_singleton_iff.mp hx).symm⟩
  have hd := finrank_span_eq_card hi
  rw [hr, Fintype.card_fin] at hd
  exact hd

theorem conjugateRootPlane_finrank (s : ℕ) (g : elementaryRootGroup K (s + 3)) :
    Module.finrank K (conjugateRootPlane (K := K) s g) = 2 := by
  let e : (Index (s + 3) → K) ≃ₗ[K] (Index (s + 3) → K) :=
    { toLinearMap := Matrix.mulVecLin (g.val : Mat K (s + 3))
      invFun := fun v => (↑(g.val⁻¹) : Mat K (s + 3)) *ᵥ v
      left_inv := by
        intro v
        change (↑(g.val⁻¹) : Mat K (s + 3)) *ᵥ ((g.val : Mat K (s + 3)) *ᵥ v) = v
        rw [Matrix.mulVec_mulVec, Units.inv_mul, Matrix.one_mulVec]
      right_inv := by
        intro v
        change (g.val : Mat K (s + 3)) *ᵥ ((↑(g.val⁻¹) : Mat K (s + 3)) *ᵥ v) = v
        rw [Matrix.mulVec_mulVec, Units.mul_inv, Matrix.one_mulVec] }
  exact (e.finrank_map_eq (standardRootPlane (K := K) s)).trans (standardRootPlane_finrank s)

theorem singular_two_plane_iff_conjugateRootPlane (h2 : (2 : K) ≠ 0) (s : ℕ)
    (P : Submodule K (Index (s + 3) → K)) :
    (Module.finrank K P = 2 ∧ IsTotallySingular (K := K) s P) ↔
      ∃ g : elementaryRootGroup K (s + 3), P = conjugateRootPlane (K := K) s g := by
  constructor
  · rintro ⟨hd, hs⟩
    exact exists_conjugateRootPlane_of_totallySingular h2 s P hd hs
  · rintro ⟨g, rfl⟩
    exact ⟨conjugateRootPlane_finrank s g, conjugateRootPlane_totallySingular h2 s g⟩

end SymmetricSubgroupAsymptotics.CFSGOrthogonalBUnipotent
