import SymmetricSubgroupAsymptotics.BinaryFourAffineImage
import SymmetricSubgroupAsymptotics.InvariantEmbeddingPermutationAction
import Mathlib.GroupTheory.SpecificGroups.Cyclic.Basic

/-! The five two-dimensional planes of one binary four-space spread.
Fixing all five planes forces a linear map to be one of the three scalar
maps. The finite calculation considers three possible images for each
basis vector, not all linear maps or any subgroup enumeration. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped BigOperators Classical

namespace SymmetricSubgroupAsymptotics
namespace BinaryFourProjectiveSpread

abbrev Vector := BinaryFourAffineImage.Vector
abbrev LinearGroup := BinaryFourAffineImage.LinearGroup

def basisVector (i : Fin 4) : Vector := Pi.single i 1

def planeVectors (i : Fin 5) (j : Fin 3) : Vector :=
  binaryVectorOfMask 4 (![![(1 : ℕ), 2, 3], ![4, 8, 12], ![5, 10, 15],
    ![13, 11, 6], ![9, 7, 14]] i j)

def plane (i : Fin 5) : Finset Vector := Finset.univ.image (planeVectors i)

def scalar : LinearGroup where
  toFun v := ![v 0 + v 1, v 0, v 2 + v 3, v 2]
  invFun v := ![v 1, v 0 + v 1, v 3, v 2 + v 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel
  map_add' := by decide +kernel
  map_smul' := by decide +kernel

def linearPerm : LinearGroup →* Equiv.Perm Vector where
  toFun r := r.toEquiv
  map_one' := rfl
  map_mul' _ _ := rfl

def planeAction : LinearGroup →* Equiv.Perm (Finset Vector) :=
  (InvariantEmbeddingPermutationAction.finsetHom Vector).comp linearPerm

theorem plane_injective : Function.Injective plane := by decide +kernel

theorem planeVectors_mem (i : Fin 5) (j : Fin 3) : planeVectors i j ∈ plane i :=
  Finset.mem_image.mpr ⟨j, Finset.mem_univ j, rfl⟩

theorem basisVector_mem : ∀ i : Fin 4,
    basisVector i ∈ plane (if i.val < 2 then 0 else 1) := by decide +kernel

def applyColumns (c : Fin 4 → Vector) (v : Vector) : Vector := ∑ i, v i • c i

theorem vector_decomposition : ∀ v : Vector, ∑ i, v i • basisVector i = v := by
  decide +kernel

theorem linear_apply_columns (r : LinearGroup) (v : Vector) :
    r v = applyColumns (fun i ↦ r (basisVector i)) v := by
  calc
    r v = r (∑ i, v i • basisVector i) := congrArg r (vector_decomposition v).symm
    _ = applyColumns (fun i ↦ r (basisVector i)) v := by
      simp only [applyColumns, map_sum, map_smul]

def columns (j : Fin 4 → Fin 3) (i : Fin 4) : Vector :=
  planeVectors (if i.val < 2 then 0 else 1) (j i)

/-- Only 3^4 choices of four images are considered. Preservation of all
three nonzero vectors in each plane already excludes singular choices. -/
theorem columns_classification : ∀ j : Fin 4 → Fin 3,
    (∀ i : Fin 5, ∀ k : Fin 3,
      applyColumns (columns j) (planeVectors i k) ∈ plane i) →
    (∀ v : Vector, applyColumns (columns j) v = v) ∨
      (∀ v : Vector, applyColumns (columns j) v = scalar v) ∨
      (∀ v : Vector, applyColumns (columns j) v = (scalar ^ 2) v) := by
  decide +kernel

theorem fixed_classification (r : LinearGroup)
    (h : ∀ i : Fin 5, planeAction r (plane i) = plane i) :
    r = 1 ∨ r = scalar ∨ r = scalar ^ 2 := by
  have hmem (i : Fin 5) (v : Vector) (hv : v ∈ plane i) : r v ∈ plane i := by
    rw [← h i]
    exact Finset.mem_map.mpr ⟨v, hv, rfl⟩
  have hex (i : Fin 4) : ∃ k : Fin 3,
      r (basisVector i) = planeVectors (if i.val < 2 then 0 else 1) k := by
    obtain ⟨k, _hk, heq⟩ := Finset.mem_image.mp (hmem _ _ (basisVector_mem i))
    exact ⟨k, heq.symm⟩
  choose j hj using hex
  have heval (v : Vector) : r v = applyColumns (columns j) v := by
    rw [linear_apply_columns]
    unfold applyColumns
    apply Finset.sum_congr rfl
    intro i _hi
    change v i • r (basisVector i) = v i • columns j i
    rw [hj i]
    rfl
  have hcheck : ∀ i : Fin 5, ∀ k : Fin 3,
      applyColumns (columns j) (planeVectors i k) ∈ plane i := by
    intro i k
    rw [← heval]
    exact hmem i _ (planeVectors_mem i k)
  rcases columns_classification j hcheck with h1 | hs | hs2
  · left
    apply LinearEquiv.ext
    intro v
    exact (heval v).trans (h1 v)
  · right; left
    apply LinearEquiv.ext
    intro v
    exact (heval v).trans (hs v)
  · right; right
    apply LinearEquiv.ext
    intro v
    exact (heval v).trans (hs2 v)

theorem fixed_mem_zpowers (r : LinearGroup)
    (h : ∀ i : Fin 5, planeAction r (plane i) = plane i) :
    r ∈ Subgroup.zpowers scalar := by
  rcases fixed_classification r h with h | h | h
  · rw [h]; exact (Subgroup.zpowers scalar).one_mem
  · rw [h]; exact Subgroup.mem_zpowers scalar
  · rw [h]; exact Subgroup.npow_mem_zpowers scalar 2

def spread (e : LinearGroup) (i : Fin 5) : Finset Vector := planeAction e (plane i)

theorem spread_injective (e : LinearGroup) : Function.Injective (spread e) :=
  (planeAction e).injective.comp plane_injective

/-- Any faithful linear action admitting this exact five-label action
has cyclic kernel. The supplied group and homomorphism are retained. -/
theorem action_kernel_isCyclic
    {G : Type} [Group G] (ρ : G →* LinearGroup) (hρ : Function.Injective ρ)
    (f : G →* Equiv.Perm (Fin 5)) (e : LinearGroup)
    (hact : ∀ g : G, ∀ i : Fin 5,
      planeAction (ρ g) (spread e i) = spread e (f g i)) : IsCyclic f.ker := by
  let κ₀ : f.ker →* LinearGroup :=
    (MulAut.conj e⁻¹).toMonoidHom.comp (ρ.comp f.ker.subtype)
  have hκ₀ (g : f.ker) : κ₀ g ∈ Subgroup.zpowers scalar := by
    apply fixed_mem_zpowers
    intro i
    have hg : f g.1 = 1 := g.2
    have hi : planeAction (ρ g.1) (spread e i) = spread e i := by
      rw [hact, hg]
      rfl
    change planeAction (e⁻¹ * ρ g.1 * e) (plane i) = plane i
    calc
      planeAction (e⁻¹ * ρ g.1 * e) (plane i) =
          planeAction e⁻¹ (planeAction (ρ g.1) (planeAction e (plane i))) := by
        simp only [map_mul, Equiv.Perm.mul_apply]
      _ = planeAction e⁻¹ (planeAction e (plane i)) := congrArg (planeAction e⁻¹) hi
      _ = plane i := by rw [map_inv]; exact (planeAction e).symm_apply_apply _
  let κ : f.ker →* Subgroup.zpowers scalar := κ₀.codRestrict _ hκ₀
  apply isCyclic_of_injective κ
  intro x y hxy
  apply Subtype.ext
  apply hρ
  apply (MulAut.conj e⁻¹).injective
  exact congrArg Subtype.val hxy

end BinaryFourProjectiveSpread
end SymmetricSubgroupAsymptotics

end
