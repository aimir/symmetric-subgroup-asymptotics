import Mathlib.Algebra.Group.Subgroup.Map
import Mathlib.Algebra.Group.Commute.Hom

/-! Elementwise commutation of two literal subgroups is preserved and
reflected by injective group maps. -/
set_option autoImplicit false
namespace SymmetricSubgroupAsymptotics.CFSGSubgroupPairCommutation

def AllCommute {G : Type*} [Group G] (P Q : Subgroup G) : Prop :=
  ∀ x ∈ P, ∀ y ∈ Q, Commute x y

theorem allCommute_map_iff {G H : Type*} [Group G] [Group H]
    (f : G →* H) (hf : Function.Injective f) (P Q : Subgroup G) :
    AllCommute (P.map f) (Q.map f) ↔ AllCommute P Q := by
  constructor
  · intro h x hx y hy
    apply hf
    simpa only [map_mul] using (h (f x) ⟨x, hx, rfl⟩ (f y) ⟨y, hy, rfl⟩).eq
  · intro h
    rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩
    change f x * f y = f y * f x
    rw [← map_mul, ← map_mul, (h x hx y hy).eq]

end SymmetricSubgroupAsymptotics.CFSGSubgroupPairCommutation
