import SymmetricSubgroupAsymptotics.BinaryPairFiniteRows

/-! A complete registry of invariant subgroups inside one retained original
kernel. Local closure under adjoining the normal orbit of each kernel
point proves coverage of every original invariant kernel subspace. No
list of original normal lifts or assumption of their coverage is needed. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics

variable {G I : Type*} [Group G]

/-- Local normal-orbit joins suffice to enumerate every invariant subgroup
of the literal kernel. In a physical binary frame the point type has at
most `2^(width/2)` elements, even when the original group is much larger. -/
structure BinaryKernelNormalRegistry (K : Subgroup G) (states : I → Subgroup G) where
  normal : ∀ i, (states i).Normal
  le_kernel : ∀ i, states i ≤ K
  bottom : I
  bottom_eq : states bottom = ⊥
  child : I → K → I
  child_eq : ∀ i x, states (child i x) =
    states i ⊔ Subgroup.normalClosure ({(x : G)} : Set G)

namespace BinaryKernelNormalRegistry
variable {K : Subgroup G} {states : I → Subgroup G}
    (C : BinaryKernelNormalRegistry K states)

include C

/-- Closure of finite local point additions proves complete invariant-axis
coverage. The ambient source and its normality are retained literally. -/
theorem complete [Finite K] (N : Subgroup G) [N.Normal] (hNK : N ≤ K) :
    ∃ i, states i = N := by
  classical
  letI : Finite N := Finite.of_injective
    (fun x : N => (⟨(x:G),hNK x.property⟩ : K)) (by
      intro x y h
      exact Subtype.ext (congrArg (fun z : K => (z:G)) h))
  letI := Fintype.ofFinite N
  have extend : ∀ s : Finset N, ∃ i, states i ≤ N ∧
      ∀ x ∈ s, (x:G) ∈ states i := by
    intro s
    induction s using Finset.induction_on with
    | empty =>
      refine ⟨C.bottom,?_,by simp⟩
      rw [C.bottom_eq]
      exact bot_le
    | @insert x s hx ih =>
      obtain ⟨i,hi,hs⟩ := ih
      let k : K := ⟨(x:G),hNK x.property⟩
      refine ⟨C.child i k,?_,?_⟩
      · rw [C.child_eq]
        exact sup_le hi (Subgroup.normalClosure_le_normal (by
          intro y hy
          have he : y=(x:G) := Set.mem_singleton_iff.mp hy
          exact he ▸ x.property))
      · intro y hy
        rw [C.child_eq]
        rcases Finset.mem_insert.mp hy with rfl|hy
        · exact (show Subgroup.normalClosure ({(y:G)} : Set G) ≤ states i ⊔ Subgroup.normalClosure ({(y:G)} : Set G) from le_sup_right) (Subgroup.subset_normalClosure (Set.mem_singleton (y:G)))
        · exact (show states i ≤ states i ⊔ Subgroup.normalClosure ({(x:G)} : Set G) from le_sup_left) (hs y hy)
  obtain ⟨i,hi,hs⟩ := extend Finset.univ
  exact ⟨i,le_antisymm hi (by
    intro x hx
    exact hs ⟨x,hx⟩ (Finset.mem_univ _))⟩

end BinaryKernelNormalRegistry

/-- An actual normal with trivial top image is exactly its intersection
with the literal kernel; there is no unrecorded extension choice here. -/
theorem binary_normal_eq_intersection_of_top_trivial {T : Type*} [Group T]
    (top : G →* T) (N : Subgroup G)
    (h : N.map top = ⊥) : top.ker ⊓ N = N := by
  apply inf_eq_right.mpr
  intro x hx
  have hm : top x ∈ N.map top := ⟨x,hx,rfl⟩
  rw [h] at hm
  exact Subgroup.mem_bot.mp hm

/-- Literal kernel intersections and top images determine the kernel of
all later faithful top-quotient covers. -/
theorem binary_kernel_sup_eq_of_top_image_eq {T : Type*} [Group T]
    (top : G →* T) (N₁ N₂ : Subgroup G)
    (h : N₁.map top=N₂.map top) : top.ker ⊔ N₁=top.ker ⊔ N₂ := by
  rw [sup_comm, ← Subgroup.comap_map_eq, h, Subgroup.comap_map_eq, sup_comm]

end SymmetricSubgroupAsymptotics
