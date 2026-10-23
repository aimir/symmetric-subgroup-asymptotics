import Mathlib.GroupTheory.Sylow
import Mathlib.GroupTheory.Solvable

/-! The normalizer of a Sylow restricted to an intermediate subgroup
embeds into its original normalizer. No normality of the intermediate
subgroup is needed. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGSylowIntermediateNormalizer

theorem normalizer_soluble_subtype {G : Type*} [Group G] {p : ℕ}
    (P : Sylow p G) (R : Subgroup G) (hPR : (P : Subgroup G) ≤ R)
    (hsol : IsSolvable (Subgroup.normalizer (P : Set G))) :
    IsSolvable (Subgroup.normalizer ((P.subtype hPR : Subgroup R) : Set R)) := by
  let U := (P : Subgroup G).subgroupOf R
  let NR := Subgroup.normalizer (U : Set R)
  let NG := Subgroup.normalizer (P : Set G)
  letI : IsSolvable NG := hsol
  have hm : U.map R.subtype = (P : Subgroup G) := by
    rw [Subgroup.subgroupOf_map_subtype, inf_of_le_left hPR]
  have hN (x : NR) : x.val.val ∈ NG := by
    have hx := U.le_normalizer_map R.subtype ⟨x.val, x.property, rfl⟩
    rw [hm] at hx
    exact hx
  let f : NR →* NG :=
    { toFun := fun x => ⟨x.val.val, hN x⟩
      map_one' := rfl
      map_mul' := fun _ _ => rfl }
  apply solvable_of_solvable_injective (f := f)
  intro x y h
  apply Subtype.ext
  apply Subtype.ext
  exact congrArg (fun z : NG => z.val) h

end SymmetricSubgroupAsymptotics.CFSGSylowIntermediateNormalizer
