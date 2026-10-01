import SymmetricSubgroupAsymptotics.ActualBlockWreathEmbedding
import SymmetricSubgroupAsymptotics.PrimeCoordinateNormalHeads

/-!
# Full coordinates of a regular-top block kernel

For an actual block system, the standard wreath embedding identifies the
literal top kernel with a correlated subgroup of the product of the exact
primitive components.  If the faithful top action is free, exact-component
fullness puts every component element in that kernel.  Thus all coordinate
projections are onto while the original correlations are retained.
-/

set_option autoImplicit false
noncomputable section
open scoped Classical

namespace SymmetricSubgroupAsymptotics
namespace BlockKernelFullCoordinates

variable {A Ω X : Type} [Group A] [MulAction A Ω] [MulAction A X]
variable [MulAction.IsPretransitive A X] [FaithfulSMul A Ω]
variable (b : Ω → X) (hb : ∀ (a : A) (ω : Ω), b (a • ω) = a • b ω)
variable (x₀ : X)

abbrev Component := ActualBlockWreathEmbedding.Component b hb x₀
abbrev Top := ActualBlockWreathEmbedding.Top (A := A) (X := X)
abbrev embedding := ActualBlockWreathEmbedding.embedding b hb x₀

/-- Forget the local component while retaining the actual top. -/
def trivialComponent : Component b hb x₀ →* PUnit := 1

/-- The kernel of the top coordinate in the actual wreath embedding. -/
abbrev Kernel : Subgroup A :=
  PermutationalWreathProduct.Compression.kernel
    (embedding b hb x₀) (trivialComponent b hb x₀)

/-- A literal component coordinate of the correlated block kernel. -/
def coordinate (x : X) : Kernel b hb x₀ →* Component b hb x₀ :=
  (trivialComponent b hb x₀).ker.subtype.comp
    (PermutationalWreathProduct.Compression.kernelCoordinate
      (embedding b hb x₀) (trivialComponent b hb x₀) x)

/-- The wreath coordinates jointly retain the original block kernel. -/
theorem coordinates_injective :
    Function.Injective (fun k x => coordinate b hb x₀ x k) := by
  intro k l hkl
  apply PermutationalWreathProduct.Compression.kernelCoordinate_joint_injective
    (embedding b hb x₀) (trivialComponent b hb x₀)
    (ActualBlockWreathEmbedding.embedding_injective b hb x₀)
  funext x
  apply Subtype.ext
  exact congrFun hkl x

/-- The compressed kernel is exactly the kernel of the original faithful
top map. -/
theorem kernel_eq_topMap_ker :
    Kernel b hb x₀ = (MulAction.toPermHom A X).ker := by
  ext a
  constructor
  · intro ha
    have hw := (PermutationalWreathProduct.mem_mapBase_ker_iff
      (trivialComponent b hb x₀) (embedding b hb x₀ a)).mp ha
    exact congrArg Subtype.val hw.1
  · intro ha
    apply (PermutationalWreathProduct.mem_mapBase_ker_iff
      (trivialComponent b hb x₀) (embedding b hb x₀ a)).mpr
    refine ⟨?_, ?_⟩
    · apply Subtype.ext
      exact MonoidHom.mem_ker.mp ha
    intro x
    exact MonoidHom.mem_ker.mpr (Subsingleton.elim _ _)

/-- If no nonidentity top element fixes a block, every exact component
element is realized by an element of the literal top kernel. -/
theorem coordinate_surjective_of_free
    (hfree : ∀ (q : Top (A := A) (X := X)) (x : X), q • x = x → q = 1)
    (x : X) : Function.Surjective (coordinate b hb x₀ x) := by
  intro d
  obtain ⟨a, hfix, hcoord⟩ :=
    ActualBlockWreathEmbedding.fullComponent b hb x₀ x d
  have htop : (embedding b hb x₀ a).right = 1 :=
    hfree (embedding b hb x₀ a).right x hfix
  have ha : a ∈ Kernel b hb x₀ := by
    apply (PermutationalWreathProduct.mem_mapBase_ker_iff
      (trivialComponent b hb x₀) (embedding b hb x₀ a)).mpr
    refine ⟨htop, ?_⟩
    intro y
    exact MonoidHom.mem_ker.mpr (Subsingleton.elim _ _)
  refine ⟨⟨a, ha⟩, ?_⟩
  exact hcoord

end BlockKernelFullCoordinates
end SymmetricSubgroupAsymptotics

end
