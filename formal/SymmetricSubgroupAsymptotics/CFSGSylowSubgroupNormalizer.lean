import SymmetricSubgroupAsymptotics.CFSGGoodSylowOfTwoPSubgroups

/-! Soluble normalizers restrict to an actual intermediate subgroup.
This uses the same literal p-subgroup, not an independently chosen Sylow. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGSylowSubgroupNormalizer
variable {G : Type*} [Group G] (U H : Subgroup G)

def normalizerInclusion (hUH : U≤H) :
    Subgroup.normalizer (U.subgroupOf H:Set H) →*
      Subgroup.normalizer (U:Set G) where
  toFun x := ⟨x.val.val,by
    have he := congrArg (fun S : Subgroup H => x.val∈S)
      (Subgroup.subgroupOf_normalizer_eq hUH)
    exact he.mpr x.property⟩
  map_one' := rfl
  map_mul' _ _ := rfl

theorem normalizerInclusion_injective (hUH : U≤H) :
    Function.Injective (normalizerInclusion U H hUH) := by
  intro x y he
  apply Subtype.ext
  apply Subtype.ext
  exact congrArg (fun z : Subgroup.normalizer (U:Set G) => z.val) he

theorem soluble_subgroup_normalizer (hUH : U≤H)
    (hsol : IsSolvable (Subgroup.normalizer (U:Set G))) :
    IsSolvable (Subgroup.normalizer (U.subgroupOf H:Set H)) := by
  letI := hsol
  exact solvable_of_solvable_injective (f := normalizerInclusion U H hUH)
    (normalizerInclusion_injective U H hUH)

end SymmetricSubgroupAsymptotics.CFSGSylowSubgroupNormalizer
