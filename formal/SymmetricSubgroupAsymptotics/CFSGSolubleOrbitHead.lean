import SymmetricSubgroupAsymptotics.CFSGSolublePrimitiveCoarse
import SymmetricSubgroupAsymptotics.LargeOrbitGeneratorConsequencesHead

/-! The actual supported primitive head has a quadratic logarithmic cost,
without a published primitive generation hypothesis. -/
set_option autoImplicit false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics.CFSGSolubleOrbitConsequences
open MarkedC4 LargeOrbitGeneratorConsequences
variable {G X : Type} [Group G] [Finite G] [IsSolvable G]
  [Fintype X] [Nonempty X] {S : ActionShape}

theorem primitive_head_generator_bound
    (f : G →* (ActionShape.cons X S).Coordinates)
    (hf : Function.Injective f)
    (hprimitive : letI : MulAction G X := MulAction.compHom X (ActionShape.head f)
      MulAction.IsPreprimitive G X)
    (hr : 2 ≤ Fintype.card X) :
    (genRank G : ℝ) ≤ genRank (ActionShape.tail f).range +
      ((Real.logb 2 (Fintype.card X))^2 + Real.logb 2 (Fintype.card X)) := by
  let h := ActionShape.head f
  let t := ActionShape.tail f
  let U := h.range
  let q : G →* U := h.rangeRestrict
  let L := t.ker
  let N : Subgroup U := L.map q
  letI : IsSolvable U := solvable_of_surjective (f := q) h.rangeRestrict_surjective
  letI : MulAction G X := MulAction.compHom X h
  letI : Nontrivial X := Fintype.one_lt_card_iff_nontrivial.mp (by omega)
  let eX : X →ₑ[q] X := { toFun := id, map_smul' := by intros; rfl }
  letI : MulAction.IsPreprimitive U X :=
    (MulAction.isPreprimitive_congr h.rangeRestrict_surjective
      (show Function.Bijective eX from Function.bijective_id)).mp hprimitive
  let k : L →* N := q.subgroupMap L
  have hk : Function.Injective k := by
    intro a b hab
    apply Subtype.ext
    apply hf
    apply Prod.ext
    · exact congrArg (fun z : N => ((z : U) : Equiv.Perm X)) hab
    · exact a.2.trans b.2.symm
  let e := MulEquiv.ofBijective k ⟨hk, q.subgroupMap_surjective L⟩
  have hL : (genRank L : ℝ) ≤
      (Real.logb 2 (Fintype.card X))^2 + Real.logb 2 (Fintype.card X) := by
    have hN := CFSGSolublePrimitiveCoarse.subgroup_rank (G := U) (X := X) N
    have hE := (genRank_le_of_surjective e.symm.toMonoidHom e.symm.surjective).trans
      (genRank_le_groupRank N)
    have hER : (genRank L : ℝ) ≤ Group.rank N := by exact_mod_cast hE
    simpa only [Nat.card_eq_fintype_card] using hER.trans hN
  have ht := genRank_le_kernel_add_range t
  have htR : (genRank G : ℝ) ≤ genRank t.ker + genRank t.range := by exact_mod_cast ht
  change (genRank t.ker : ℝ) ≤ _ at hL
  change (genRank G : ℝ) ≤ genRank t.range + _
  linarith

end SymmetricSubgroupAsymptotics.CFSGSolubleOrbitConsequences
