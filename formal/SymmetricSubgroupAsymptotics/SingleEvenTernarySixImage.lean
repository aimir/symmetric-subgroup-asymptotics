import SymmetricSubgroupAsymptotics.TwoAxisSixActualUpper
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.SingleEvenTernarySixImage
open SemidirectProduct
abbrev Ternary := TernarySwapUpperNormalGenerators.Ternary
abbrev Binary := TernarySwapUpperNormalGenerators.Binary
abbrev Local := SixPointTernaryAxesNormalGenerators.Local
abbrev Model := Ternary × Local

def embed : Model →* SixPointTernaryAxesNormalGenerators.Model :=
  (inl : Ternary →* Local).prodMap (MonoidHom.id Local)
def action : Model →* Equiv.Perm (Fin 6) := SixPointTernaryAxesNormalGenerators.literalAction.comp embed

theorem embed_injective : Function.Injective embed := by
  intro x y h
  apply Prod.ext
  · exact congrArg (fun z : SixPointTernaryAxesNormalGenerators.Model => z.1.left) h
  · exact congrArg (fun z : SixPointTernaryAxesNormalGenerators.Model => z.2) h
theorem action_injective : Function.Injective action :=
  TwoAxisSixActualUpper.action_injective.comp embed_injective

def canonicalEquiv : Model ≃* action.range :=
  MulEquiv.ofBijective action.rangeRestrict
    ⟨fun _ _ h => action_injective (congrArg Subtype.val h),action.rangeRestrict_surjective⟩
theorem range_card : Nat.card action.range=18 := by
  rw [← Nat.card_congr canonicalEquiv.toEquiv,Nat.card_prod,
    Nat.card_congr (SemidirectProduct.equivProd : Local ≃ Ternary × Binary),Nat.card_prod]
  norm_num [Ternary,Binary,TernarySwapUpperNormalGenerators.Ternary,
    TernarySwapUpperNormalGenerators.Binary,Nat.card_eq_fintype_card]
theorem range_le : action.range≤SixPointTernaryAxesNormalGenerators.literalAction.range := by
  rintro _ ⟨g,rfl⟩
  exact ⟨embed g,rfl⟩

theorem subgroup_card (P : Subgroup (Equiv.Perm (Fin 6))) (hle : P≤action.range) : Nat.card P∣18 := by
  simpa only [range_card] using Subgroup.card_dvd_of_le hle

theorem isSolvable (P : Subgroup (Equiv.Perm (Fin 6))) (hle : P≤action.range) : IsSolvable P := by
  let beta := TwoAxisSixActualUpper.projection P (hle.trans range_le)
  have hodd : IsPGroup 3 beta.ker := TwoAxisSixActualUpper.kernel_isPGroup P (hle.trans range_le)
  letI : Group.IsNilpotent beta.ker := hodd.isNilpotent
  exact solvable_of_ker_le_range beta.ker.subtype beta (by rw [Subgroup.range_subtype])
end SymmetricSubgroupAsymptotics.SingleEvenTernarySixImage
