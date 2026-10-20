import SymmetricSubgroupAsymptotics.LargeOrbitGeneratorConsequencesPrimitive

/-! Transport actual point actions to their full images, and bound the
ordinary kernel supported on one primitive head orbit. -/
set_option autoImplicit false
noncomputable section
open scoped Classical

namespace SymmetricSubgroupAsymptotics.LargeOrbitGeneratorConsequences
open MarkedC4

namespace ActionShape

variable {G H : Type} [Group G] [Group H]

/-- Transitivity under a homomorphic subgroup already implies transitivity
under the full group acting on the same original points. -/
theorem profile_of_comp : {S : ActionShape} →
    (f : G →* S.Coordinates) → (g : H →* G) →
    TransitiveProfile (f.comp g) → TransitiveProfile f
  | .nil, _, _, _ => trivial
  | @ActionShape.cons X _ _ S, f, g, h => by
      refine ⟨?_, profile_of_comp (tail f) g h.2⟩
      letI : MulAction G X := MulAction.compHom X (head f)
      letI : MulAction H X := MulAction.compHom X (head (f.comp g))
      letI : MulAction.IsPretransitive H X := h.1
      constructor
      intro x y
      obtain ⟨a, ha⟩ := MulAction.exists_smul_eq H x y
      exact ⟨g a, ha⟩

end ActionShape

variable {G X : Type} [Group G] [Finite G] [Fintype X] [Nonempty X]
  {S : ActionShape}

/-- The full source is bounded using the *ordinary* rank of its actual
kernel supported on a primitive head orbit.  That kernel maps injectively
to a normal subgroup of the genuine primitive head image. -/
theorem primitive_head_generator_bound
    (hgen : PrimitiveNormalGeneratorInput)
    (f : G →* (ActionShape.cons X S).Coordinates)
    (hf : Function.Injective f)
    (hprimitive : letI : MulAction G X :=
      MulAction.compHom X (ActionShape.head f)
      MulAction.IsPreprimitive G X)
    (hr : 2 ≤ Fintype.card X) :
    genRank G ≤ genRank (ActionShape.tail f).range +
      (Nat.log2 (Fintype.card X) + 2) := by
  let h := ActionShape.head f
  let t := ActionShape.tail f
  let U := h.range
  let q : G →* U := h.rangeRestrict
  let L := t.ker
  let N : Subgroup U := L.map q
  letI : N.Normal := (inferInstance : L.Normal).map q h.rangeRestrict_surjective
  letI : MulAction G X := MulAction.compHom X h
  let eX : X →ₑ[q] X := { toFun := id, map_smul' := by intros; rfl }
  have hU : MulAction.IsPreprimitive U X :=
    (MulAction.isPreprimitive_congr h.rangeRestrict_surjective
      (show Function.Bijective eX from Function.bijective_id)).mp hprimitive
  let k : L →* N := q.subgroupMap L
  have hk : Function.Injective k := by
    intro a b hab
    apply Subtype.ext
    apply hf
    apply Prod.ext
    · exact congrArg (fun z : N => ((z : U) : Equiv.Perm X)) hab
    · have ha : t a.1 = 1 := a.2
      have hb : t b.1 = 1 := b.2
      exact ha.trans hb.symm
  let e := MulEquiv.ofBijective k ⟨hk, q.subgroupMap_surjective L⟩
  have hL : genRank L ≤ Nat.log2 (Fintype.card X) + 2 := by
    have hN := primitiveNormal_genRank_bound_all hgen U hU N hr
    exact (genRank_le_of_surjective e.symm.toMonoidHom e.symm.surjective).trans hN
  have ht := genRank_le_kernel_add_range t
  change genRank t.ker ≤ Nat.log2 (Fintype.card X) + 2 at hL
  change genRank G ≤ genRank t.range + (Nat.log2 (Fintype.card X) + 2)
  calc
    genRank G ≤ genRank t.ker + genRank t.range := ht
    _ ≤ (Nat.log2 (Fintype.card X) + 2) + genRank t.range :=
      Nat.add_le_add_right hL _
    _ = genRank t.range + (Nat.log2 (Fintype.card X) + 2) := Nat.add_comm _ _

end SymmetricSubgroupAsymptotics.LargeOrbitGeneratorConsequences
