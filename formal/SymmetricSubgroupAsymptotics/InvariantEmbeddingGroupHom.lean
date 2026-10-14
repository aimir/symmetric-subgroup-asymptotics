import SymmetricSubgroupAsymptotics.InvariantEmbeddingPermutationAction

/-! Lift an invariant embedded action through any faithful permutation
representation. In particular, explicit linear witnesses on generators
produce an actual homomorphism into a linear group. -/

set_option autoImplicit false
noncomputable section

namespace SymmetricSubgroupAsymptotics
namespace InvariantEmbeddingGroupHom

variable {G H X I : Type*} [Group G] [Group H]

def liftable (ρ : G →* Equiv.Perm X) (f : I → X)
    (η : H →* Equiv.Perm I) : Subgroup G where
  carrier := {g | ∃ h : H, ∀ i, ρ g (f i) = f (η h i)}
  one_mem' := ⟨1, by intro i; simp⟩
  mul_mem' := by
    rintro g k ⟨h, hh⟩ ⟨l, hl⟩
    exact ⟨h * l, fun i => by simp only [map_mul, Equiv.Perm.mul_apply, hl, hh]⟩
  inv_mem' := by
    rintro g ⟨h, hh⟩
    refine ⟨h⁻¹, fun i => ?_⟩
    apply (ρ g).injective
    calc
      ρ g (ρ g⁻¹ (f i)) = f i := by
        rw [← Equiv.Perm.mul_apply, ← map_mul, mul_inv_cancel, map_one]
        rfl
      _ = ρ g (f (η h⁻¹ i)) := by rw [hh, map_inv]; simp

variable (ρ : G →* Equiv.Perm X) (f : I → X) (η : H →* Equiv.Perm I)
    (hf : Function.Injective f) (hη : Function.Injective η)
    (h : ∀ g, g ∈ liftable ρ f η)

def lift : G →* H where
  toFun g := Classical.choose (h g)
  map_one' := by
    apply hη
    apply Equiv.ext
    intro i
    apply hf
    simpa only [map_one, Equiv.Perm.one_apply] using
      (Classical.choose_spec (h 1) i).symm
  map_mul' g k := by
    apply hη
    apply Equiv.ext
    intro i
    apply hf
    calc
      f (η (Classical.choose (h (g * k))) i) = ρ (g * k) (f i) :=
        (Classical.choose_spec (h (g * k)) i).symm
      _ = f (η (Classical.choose (h g) * Classical.choose (h k)) i) := by
        rw [map_mul, Equiv.Perm.mul_apply, Classical.choose_spec (h k),
          Classical.choose_spec (h g), map_mul, Equiv.Perm.mul_apply]

theorem intertwine (g : G) (i : I) :
    ρ g (f i) = f (η (lift ρ f η hf hη h g) i) :=
  Classical.choose_spec (h g) i

theorem lift_eq (g : G) (k : H)
    (hk : ∀ i, ρ g (f i) = f (η k i)) : lift ρ f η hf hη h g = k := by
  apply hη
  apply Equiv.ext
  intro i
  apply hf
  exact (intertwine ρ f η hf hη h g i).symm.trans (hk i)

end InvariantEmbeddingGroupHom
end SymmetricSubgroupAsymptotics

end
