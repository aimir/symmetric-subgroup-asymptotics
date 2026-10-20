import Mathlib.Algebra.Group.Subgroup.Ker

/-! A checked source generating tuple and literal image bindings determine
the image subgroup, with the exact target tuple and ambient action retained. -/

set_option autoImplicit false
noncomputable section

namespace SymmetricSubgroupAsymptotics
namespace GeneratedLiteralImage

variable {G H : Type} [Group G] [Group H] {n : ℕ}
  (f : G →* H) (source : Fin n → G) (target : Fin n → H)
  (index : Equiv.Perm (Fin n))
  (hsource : Subgroup.closure (Set.range source) = ⊤)
  (hbinding : ∀ i, f (source i) = target (index i))

include hsource hbinding in
theorem range_eq : f.range = Subgroup.closure (Set.range target) := by
  let T := Subgroup.closure (Set.range target)
  apply le_antisymm
  · have hle : Subgroup.closure (Set.range source) ≤ T.comap f := by
      apply (Subgroup.closure_le _).mpr
      rintro _ ⟨i, rfl⟩
      change f (source i) ∈ T
      rw [hbinding]
      exact Subgroup.subset_closure (Set.mem_range_self (index i))
    rintro _ ⟨g, rfl⟩
    apply hle
    rw [hsource]
    exact Subgroup.mem_top g
  · apply (Subgroup.closure_le _).mpr
    rintro _ ⟨i, rfl⟩
    refine ⟨source (index.symm i), ?_⟩
    rw [hbinding, index.apply_symm_apply]

def toTop : G →* Subgroup.closure (Set.range target) :=
  (MulEquiv.subgroupCongr (range_eq f source target index hsource hbinding)).toMonoidHom.comp
    f.rangeRestrict

theorem toTop_surjective :
    Function.Surjective (toTop f source target index hsource hbinding) :=
  (MulEquiv.subgroupCongr (range_eq f source target index hsource hbinding)).surjective.comp
    f.rangeRestrict_surjective

end GeneratedLiteralImage
end SymmetricSubgroupAsymptotics

end
