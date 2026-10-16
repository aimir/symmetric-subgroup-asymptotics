import SymmetricSubgroupAsymptotics.BinaryFourAmbientBottom

/-! In an actual Klein-trivial section of a non-bottom invariant
submodule, the literal bottom plane vanishes. The target need not split
from its source; the map and its kernel are the original ones. -/

set_option autoImplicit false
noncomputable section

namespace SymmetricSubgroupAsymptotics.BinaryFourBlockAugmentation

theorem nonbottom_difference_nonzero (w : Module)
    (hw : ¬ ∃ a : Local, w = diagonal a) :
    ambientDifferenceU w ≠ 0 ∨ ambientDifferenceV w ≠ 0 := by
  have exactIdentity : ∀ w : Module, (¬ ∃ a : Local, w = diagonal a) →
      ambientDifferenceU w ≠ 0 ∨ ambientDifferenceV w ≠ 0 := by decide +kernel
  exact exactIdentity w hw

/-- A map from E to an actual Klein-trivial target kills the diagonal
whenever E contains a vector outside the diagonal. Equivariance is only
required for the displayed ternary generator. -/
theorem klein_trivial_map_kills_diagonal
    (E : Submodule Scalar Module)
    (hU : ∀ w ∈ E, ambientDifferenceU w ∈ E)
    (hV : ∀ w ∈ E, ambientDifferenceV w ∈ E)
    (hC : ∀ w ∈ E, ambientCycle w ∈ E)
    (w : Module) (hw : w ∈ E) (hnotbottom : ¬ ∃ a : Local, w = diagonal a)
    {W : Type} [AddCommGroup W] [_root_.Module Scalar W]
    (f : E →ₗ[Scalar] W) (T : W →ₗ[Scalar] W)
    (hfU : ∀ x : E, f ⟨ambientDifferenceU x, hU x x.2⟩ = 0)
    (hfV : ∀ x : E, f ⟨ambientDifferenceV x, hV x x.2⟩ = 0)
    (hfC : ∀ x : E, f ⟨ambientCycle x, hC x x.2⟩ = T (f x))
    (a : Local) :
    ∃ ha : diagonal a ∈ E, f ⟨diagonal a, ha⟩ = 0 := by
  let K : Submodule Scalar Module := (LinearMap.ker f).map E.subtype
  have memK (x : Module) (hx : x ∈ E) (hf : f ⟨x, hx⟩ = 0) : x ∈ K :=
    Submodule.mem_map.mpr ⟨⟨x, hx⟩, hf, rfl⟩
  have hKU : ∀ x ∈ K, ambientDifferenceU x ∈ K := by
    intro x hx
    obtain ⟨y, _hy, rfl⟩ := Submodule.mem_map.mp hx
    exact memK _ (hU y y.2) (hfU y)
  have hKV : ∀ x ∈ K, ambientDifferenceV x ∈ K := by
    intro x hx
    obtain ⟨y, _hy, rfl⟩ := Submodule.mem_map.mp hx
    exact memK _ (hV y y.2) (hfV y)
  have hKC : ∀ x ∈ K, ambientCycle x ∈ K := by
    intro x hx
    obtain ⟨y, hy, rfl⟩ := Submodule.mem_map.mp hx
    apply memK _ (hC y y.2)
    rw [hfC y, show f y = 0 from hy, map_zero]
  have hKne : K ≠ ⊥ := by
    rcases nonbottom_difference_nonzero w hnotbottom with h | h
    · intro hbot
      have hx := memK _ (hU w hw) (hfU ⟨w, hw⟩)
      rw [hbot] at hx
      exact h hx
    · intro hbot
      have hx := memK _ (hV w hw) (hfV ⟨w, hw⟩)
      rw [hbot] at hx
      exact h hx
  have hdiag := diagonal_mem_of_ne_bot K hKne hKU hKV hKC a
  obtain ⟨x, hx, hxa⟩ := Submodule.mem_map.mp hdiag
  have ha : diagonal a ∈ E := hxa ▸ x.2
  refine ⟨ha, ?_⟩
  have heq : x = (⟨diagonal a, ha⟩ : E) := Subtype.ext hxa
  simpa only [← heq] using hx

end SymmetricSubgroupAsymptotics.BinaryFourBlockAugmentation

end
