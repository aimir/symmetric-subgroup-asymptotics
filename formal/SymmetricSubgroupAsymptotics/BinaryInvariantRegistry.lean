import Mathlib.RepresentationTheory.Subrepresentation
import Mathlib.LinearAlgebra.FiniteDimensional.Basic

/-! Independent finite certificates for every invariant axis of one
retained binary module. Completeness follows from finite point additions;
it is not an assumption that the supplied list covers all submodules. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics

variable {k G V I : Type*} [Field k] [Monoid G] [AddCommGroup V] [Module k V]

/-- The span of an actual point's full original action orbit. -/
def binaryOrbitSpan (ρ : Representation k G V) (v : V) : Submodule k V :=
  Submodule.span k (Set.range (fun g => ρ g v))

theorem binaryOrbitSpan_le (ρ : Representation k G V) (W : Subrepresentation ρ)
    {v : V} (hv : v∈W) : binaryOrbitSpan ρ v ≤ W.toSubmodule := by
  apply Submodule.span_le.mpr
  rintro _ ⟨g,rfl⟩
  exact W.apply_mem_toSubmodule g hv

theorem binaryOrbitSpan_point (ρ : Representation k G V) (v : V) :
    v∈binaryOrbitSpan ρ v := by
  apply Submodule.subset_span
  exact ⟨1,by simp⟩

/-- Each local join has a checked literal orbit-span equality. The point
set is only the retained module, not the much larger original group. -/
structure BinaryInvariantRegistry (ρ : Representation k G V)
    (states : I → Subrepresentation ρ) where
  bottom : I
  bottom_eq : (states bottom).toSubmodule=⊥
  child : I → V → I
  child_eq : ∀ i v, (states (child i v)).toSubmodule=
    (states i).toSubmodule ⊔ binaryOrbitSpan ρ v

namespace BinaryInvariantRegistry
variable {ρ : Representation k G V} {states : I → Subrepresentation ρ}
    (C : BinaryInvariantRegistry ρ states)
include C

/-- Every actual invariant subspace is covered by the local finite
certificate, including axes that are not seen in an enumerated normal
lift dataset. -/
theorem complete [Finite V] (W : Subrepresentation ρ) : ∃ i, states i=W := by
  classical
  letI := Fintype.ofFinite W
  have extend : ∀ s : Finset W, ∃ i, (states i).toSubmodule≤W.toSubmodule ∧
      ∀ x∈s, (x:V)∈(states i).toSubmodule := by
    intro s
    induction s using Finset.induction_on with
    | empty =>
      refine ⟨C.bottom,?_,by simp⟩
      rw [C.bottom_eq]
      exact bot_le
    | @insert x s hx ih =>
      obtain ⟨i,hi,hs⟩ := ih
      refine ⟨C.child i x,?_,?_⟩
      · rw [C.child_eq]
        exact sup_le hi (binaryOrbitSpan_le ρ W x.property)
      · intro y hy
        rw [C.child_eq]
        rcases Finset.mem_insert.mp hy with rfl|hy
        · exact (show binaryOrbitSpan ρ (y:V)≤
            (states i).toSubmodule⊔binaryOrbitSpan ρ (y:V) from le_sup_right)
              (binaryOrbitSpan_point ρ y)
        · exact (show (states i).toSubmodule≤
            (states i).toSubmodule⊔binaryOrbitSpan ρ (x:V) from le_sup_left) (hs y hy)
  obtain ⟨i,hi,hs⟩ := extend Finset.univ
  refine ⟨i,Subrepresentation.toSubmodule_injective (le_antisymm hi ?_)⟩
  intro x hx
  exact hs ⟨x,hx⟩ (Finset.mem_univ _)

end BinaryInvariantRegistry

/-- The same local closure criterion restricted to one retained correlated
kernel. Points outside the original kernel never enter the certificate. -/
structure BinaryInvariantKernelRegistry (ρ : Representation k G V)
    (K : Subrepresentation ρ) (states : I → Subrepresentation ρ) where
  le_kernel : ∀ i, (states i).toSubmodule ≤ K.toSubmodule
  bottom : I
  bottom_eq : (states bottom).toSubmodule=⊥
  child : I → K → I
  child_eq : ∀ i v, (states (child i v)).toSubmodule=
    (states i).toSubmodule ⊔ binaryOrbitSpan ρ (v:V)

namespace BinaryInvariantKernelRegistry
variable {ρ : Representation k G V} {K : Subrepresentation ρ}
    {states : I → Subrepresentation ρ} (C : BinaryInvariantKernelRegistry ρ K states)
include C

theorem complete [Finite V] (W : Subrepresentation ρ)
    (hWK : W.toSubmodule≤K.toSubmodule) : ∃ i, states i=W := by
  classical
  letI := Fintype.ofFinite W
  have extend : ∀ s : Finset W, ∃ i, (states i).toSubmodule≤W.toSubmodule ∧
      ∀ x∈s, (x:V)∈(states i).toSubmodule := by
    intro s
    induction s using Finset.induction_on with
    | empty =>
      refine ⟨C.bottom,?_,by simp⟩
      rw [C.bottom_eq]
      exact bot_le
    | @insert x s hx ih =>
      obtain ⟨i,hi,hs⟩ := ih
      let v : K := ⟨(x:V),hWK x.property⟩
      refine ⟨C.child i v,?_,?_⟩
      · rw [C.child_eq]
        exact sup_le hi (binaryOrbitSpan_le ρ W x.property)
      · intro y hy
        rw [C.child_eq]
        rcases Finset.mem_insert.mp hy with he|hy
        · subst y
          exact (show binaryOrbitSpan ρ (v:V)≤
            (states i).toSubmodule⊔binaryOrbitSpan ρ (v:V) from le_sup_right)
              (binaryOrbitSpan_point ρ v)
        · exact (show (states i).toSubmodule≤
            (states i).toSubmodule⊔binaryOrbitSpan ρ (v:V) from le_sup_left) (hs y hy)
  obtain ⟨i,hi,hs⟩ := extend Finset.univ
  refine ⟨i,Subrepresentation.toSubmodule_injective (le_antisymm hi ?_)⟩
  intro x hx
  exact hs ⟨x,hx⟩ (Finset.mem_univ _)

end BinaryInvariantKernelRegistry
end SymmetricSubgroupAsymptotics
