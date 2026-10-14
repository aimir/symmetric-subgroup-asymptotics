import Mathlib.Algebra.Group.End
import Mathlib.Algebra.Group.Subgroup.Basic
import Mathlib.Data.Finset.Image

/-! Restrict a permutation action to an explicitly embedded invariant set.
The liftable elements form a subgroup, so invariance need only be checked
on generators. No enumeration or cardinality of the acting group is used. -/

set_option autoImplicit false
noncomputable section

namespace SymmetricSubgroupAsymptotics
namespace InvariantEmbeddingPermutationAction

variable {G X I : Type*} [Group G]

def liftable (ρ : G →* Equiv.Perm X) (f : I → X) : Subgroup G where
  carrier := {g | ∃ σ : Equiv.Perm I, ∀ i, ρ g (f i) = f (σ i)}
  one_mem' := ⟨1, by intro i; simp⟩
  mul_mem' := by
    rintro g h ⟨σ, hσ⟩ ⟨τ, hτ⟩
    exact ⟨σ * τ, fun i => by simp only [map_mul, Equiv.Perm.mul_apply, hτ, hσ]⟩
  inv_mem' := by
    rintro g ⟨σ, hσ⟩
    refine ⟨σ⁻¹, fun i => ?_⟩
    apply (ρ g).injective
    calc
      ρ g (ρ g⁻¹ (f i)) = f i := by
        rw [← Equiv.Perm.mul_apply, ← map_mul, mul_inv_cancel, map_one]
        rfl
      _ = ρ g (f (σ⁻¹ i)) := by rw [hσ]; simp

variable (ρ : G →* Equiv.Perm X) (f : I → X) (hf : Function.Injective f)
    (h : ∀ g, g ∈ liftable ρ f)

def lift : G →* Equiv.Perm I where
  toFun g := Classical.choose (h g)
  map_one' := by
    apply Equiv.ext
    intro i
    apply hf
    simpa only [map_one, Equiv.Perm.one_apply] using
      (Classical.choose_spec (h 1) i).symm
  map_mul' g k := by
    apply Equiv.ext
    intro i
    apply hf
    calc
      f (Classical.choose (h (g * k)) i) = ρ (g * k) (f i) :=
        (Classical.choose_spec (h (g * k)) i).symm
      _ = f (Classical.choose (h g) (Classical.choose (h k) i)) := by
        rw [map_mul, Equiv.Perm.mul_apply, Classical.choose_spec (h k),
          Classical.choose_spec (h g)]

theorem intertwine (g : G) (i : I) : ρ g (f i) = f (lift ρ f hf h g i) :=
  Classical.choose_spec (h g) i

theorem lift_eq (g : G) (σ : Equiv.Perm I)
    (hσ : ∀ i, ρ g (f i) = f (σ i)) : lift ρ f hf h g = σ := by
  apply Equiv.ext
  intro i
  apply hf
  exact (intertwine ρ f hf h g i).symm.trans (hσ i)

/-- The functorial action of permutations on finite subsets. -/
def finsetHom (X : Type*) : Equiv.Perm X →* Equiv.Perm (Finset X) where
  toFun σ := σ.finsetCongr
  map_one' := Equiv.finsetCongr_refl
  map_mul' σ τ := (Equiv.finsetCongr_trans τ σ).symm

end InvariantEmbeddingPermutationAction
end SymmetricSubgroupAsymptotics

end
