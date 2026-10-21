import Mathlib.Algebra.Group.Conj
import Mathlib.Algebra.Group.Subgroup.Ker
import Mathlib.GroupTheory.Subgroup.Simple

/-! A representation of the automorphism group is faithful as soon as its
restriction to inner automorphisms is faithful. For a simple source group,
one moved object is enough to verify this restriction. -/
set_option autoImplicit false
namespace SymmetricSubgroupAsymptotics.CFSGInnerActionFaithfulness
variable {G P : Type*} [Group G] [Group P]

theorem conj_automorphism (a : MulAut G) (g : G) :
    MulAut.conj (a g) = a * MulAut.conj g * a⁻¹ := by
  ext x
  simp [MulAut.conj_apply]

theorem injective_of_inner_injective (pi : MulAut G →* P)
    (hinner : Function.Injective (pi.comp (MulAut.conj : G →* MulAut G))) :
    Function.Injective pi := by
  intro a b hab
  ext g
  apply hinner
  change pi (MulAut.conj (a g)) = pi (MulAut.conj (b g))
  simp only [conj_automorphism, map_mul, map_inv, hab]

theorem injective_of_inner_nontrivial [IsSimpleGroup G] (pi : MulAut G →* P)
    (hmoved : ∃ g : G, pi (MulAut.conj g) ≠ 1) : Function.Injective pi := by
  apply injective_of_inner_injective pi
  let inner := pi.comp (MulAut.conj : G →* MulAut G)
  rcases (inferInstance : inner.ker.Normal).eq_bot_or_eq_top with hbot | htop
  · exact inner.ker_eq_bot_iff.mp hbot
  · obtain ⟨g, hg⟩ := hmoved
    have hmem : g ∈ inner.ker := by rw [htop]; trivial
    exact False.elim (hg hmem)

end SymmetricSubgroupAsymptotics.CFSGInnerActionFaithfulness
