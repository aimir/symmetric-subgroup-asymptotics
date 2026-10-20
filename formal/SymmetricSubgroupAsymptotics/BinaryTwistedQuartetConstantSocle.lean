import SymmetricSubgroupAsymptotics.BinaryTwistedQuartetLoewyAugmentations

/-! The constant-plane layer is one genuine binary cubic simple. A
single nonzero augmentation therefore generates the entire layer under
the actual top-three action, without extra scalar-stability premises. -/
set_option autoImplicit false
namespace SymmetricSubgroupAsymptotics.BinaryTwistedQuartetConstantSocle
open BinaryTwistedQuartetPolynomial (Bit Plane cubic)
open BinaryTwistedQuartetLoewyCoordinates

private theorem cubic_spans : ∀ u v : Plane, u≠0 →
    ∃ a b : Bit, v=a • u+b • cubic u := by decide +kernel

theorem all_constants_mem (W : Submodule Bit Space)
    (hcycle : ∀ v, v∈W → cycleAction v∈W)
    (u : Plane) (hu : u≠0) (hmem : constant u∈W) :
    ∀ v : Plane, constant v∈W := by
  have hc : constant (cubic u)∈W := by
    rw [← cycle_constant]
    exact hcycle _ hmem
  intro v
  obtain ⟨a,b,hv⟩ := cubic_spans u v hu
  rw [hv]
  change a • constant u+b • constant (cubic u)∈W
  exact W.add_mem (W.smul_mem a hmem) (W.smul_mem b hc)

end SymmetricSubgroupAsymptotics.BinaryTwistedQuartetConstantSocle
