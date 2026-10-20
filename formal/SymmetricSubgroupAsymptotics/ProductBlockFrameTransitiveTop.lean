import SymmetricSubgroupAsymptotics.ProductBlockFrameGenerators
import SymmetricSubgroupAsymptotics.TransitiveFourBinaryOrAlternating

/-! Transitivity of the original point action transfers to the actual block
image. Its four-point image can therefore enter the structural top split. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.ProductBlockFrame
variable {X I F : Type} {U : Subgroup (Equiv.Perm X)}
  (C : ProductBlockFrame U I F) [Nonempty F]

include C in
theorem top_range_transitive
    (htrans : ∀ x y : X, ∃ u : U, (u : Equiv.Perm X) x=y) :
    ∀ i j : I, ∃ g : C.top.range, (g : Equiv.Perm I) i=j := by
  intro i j
  obtain ⟨x⟩ := ‹Nonempty F›
  obtain ⟨u,hu⟩ := htrans (C.frame (i,x)) (C.frame (j,x))
  refine ⟨⟨C.top u,⟨u,rfl⟩⟩,?_⟩
  have h := C.intertwine u (i,x)
  rw [hu, C.frame.symm_apply_apply] at h
  exact h.symm

end SymmetricSubgroupAsymptotics.ProductBlockFrame
namespace SymmetricSubgroupAsymptotics.ProductBlockFrame
variable {X F : Type} {U : Subgroup (Equiv.Perm X)}
  (C : ProductBlockFrame U (Fin 4) F) [Nonempty F]

/-- Classify the actual top image without attaching a catalogue label. -/
theorem top_binary_or_alternating
    (htrans : ∀ x y : X, ∃ u : U, (u : Equiv.Perm X) x=y) :
    IsPGroup 2 C.top.range ∨ alternatingGroup (Fin 4)≤C.top.range :=
  TransitiveFourBinaryOrAlternating.binary_or_alternating C.top.range
    (C.top_range_transitive htrans)
end SymmetricSubgroupAsymptotics.ProductBlockFrame
