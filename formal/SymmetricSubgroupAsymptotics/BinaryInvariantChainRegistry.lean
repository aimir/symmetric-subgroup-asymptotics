import SymmetricSubgroupAsymptotics.BinaryInvariantRegistry

/-! A finite chain of actual cyclic orbit-spaces covers every invariant
submodule. The chain condition replaces a table of point-adjunction joins;
the proof still retains every original vector and the full acting group. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics

variable {k G V I : Type*} [Field k] [Monoid G]
    [AddCommGroup V] [Module k V] [Finite V]

theorem binaryInvariantChain_complete
    (rho : Representation k G V) (states : I → Subrepresentation rho)
    (bottom : I) (hbottom : (states bottom).toSubmodule = ⊥)
    (hchain : ∀ i j, (states i).toSubmodule ≤ (states j).toSubmodule ∨
      (states j).toSubmodule ≤ (states i).toSubmodule)
    (hpoint : ∀ v, ∃ i, (states i).toSubmodule = binaryOrbitSpan rho v)
    (W : Subrepresentation rho) : ∃ i, states i = W := by
  classical
  let point (v : V) : I := Classical.choose (hpoint v)
  have hp (v : V) : (states (point v)).toSubmodule = binaryOrbitSpan rho v :=
    Classical.choose_spec (hpoint v)
  let child (i : I) (v : V) : I :=
    if (states i).toSubmodule ≤ (states (point v)).toSubmodule then point v else i
  let C : BinaryInvariantRegistry rho states := {
    bottom := bottom
    bottom_eq := hbottom
    child := child
    child_eq i v := by
      dsimp only [child]
      split_ifs with h
      · rw [← hp v, sup_eq_right.mpr h]
      · have hi := (hchain i (point v)).resolve_left h
        rw [← hp v, sup_eq_left.mpr hi] }
  exact C.complete W

end SymmetricSubgroupAsymptotics
