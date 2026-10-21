import SymmetricSubgroupAsymptotics.CFSGPrimeOrdinaryActualDegreeProfile
import SymmetricSubgroupAsymptotics.MarkedC4ActualMarkZeroNormalRank

/-! The proved prime-permutation profile applies to arbitrary faithful
transitive actions, including the ACTUAL coprime stabilizer-coset fibres.
Passing to the original permutation image preserves ambient normal rank. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGPrimeOrdinaryActionProfile
open MarkedC4
variable {p : ℕ} [Fact p.Prime] {G X : Type} [Group G] [Finite G]
    [Finite X] [Nonempty X] [MulAction G X] [FaithfulSMul G X]
    [MulAction.IsPretransitive G X]

theorem normalGen_real_le_div (hG : IsPGroup p G) (N : Subgroup G) [N.Normal] :
    (normalGen N : ℝ) ≤ (Nat.card X : ℝ)/p := by
  let f : G →* Equiv.Perm X := MulAction.toPermHom G X
  let q := f.rangeRestrict
  have hq : Function.Surjective q := f.rangeRestrict_surjective
  have hqi : Function.Injective q := fun a b h =>
    MulAction.toPerm_injective (congrArg Subtype.val h)
  letI : MulAction.IsPretransitive f.range X := by
    constructor
    intro x y
    obtain ⟨g,hg⟩ := MulAction.exists_smul_eq G x y
    exact ⟨q g,hg⟩
  letI : (N.map q).Normal := Subgroup.Normal.map inferInstance q hq
  have he := ActualMarkZeroNormalRank.normalGen_map_eq q hq N
    (fun x _ he => hqi (he.trans (map_one q).symm))
  have hh := CFSGPrimeOrdinaryActualDegreeProfile.normalGen_real_le_div p f.range
    (hG.of_surjective q hq) (N.map q)
  rw [he] at hh
  exact hh

/-- The ternary improvement applies on the original faithful action. -/
theorem ternary_normalGen_real_le_of_degree_ne_three
    (hG : IsPGroup 3 G) (hdegree : Nat.card X≠3) (N : Subgroup G) [N.Normal] :
    (normalGen N : ℝ) ≤ (2/9 : ℝ)*Nat.card X := by
  letI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  let f : G →* Equiv.Perm X := MulAction.toPermHom G X
  let q := f.rangeRestrict
  have hq : Function.Surjective q := f.rangeRestrict_surjective
  have hqi : Function.Injective q := fun a b h =>
    MulAction.toPerm_injective (congrArg Subtype.val h)
  letI : MulAction.IsPretransitive f.range X := by
    constructor
    intro x y
    obtain ⟨g,hg⟩ := MulAction.exists_smul_eq G x y
    exact ⟨q g,hg⟩
  letI : (N.map q).Normal := Subgroup.Normal.map inferInstance q hq
  have he := ActualMarkZeroNormalRank.normalGen_map_eq q hq N
    (fun x _ he => hqi (he.trans (map_one q).symm))
  have hh := CFSGPrimeOrdinaryActualDegreeProfile.ternary_normalGen_real_le f.range
    (hG.of_surjective q hq) (N.map q)
  rw [he,if_neg (by tauto),add_zero] at hh
  exact hh

end SymmetricSubgroupAsymptotics.CFSGPrimeOrdinaryActionProfile
