import SymmetricSubgroupAsymptotics.CFSGTwistedA2FixedRadicalKernel

/-! Faithful restriction of the ORIGINAL model's opposite-pair
stabilizer to its SAME radical. The map uses the proved actual upper
projective equivalence and the proved global Sylow-action kernel. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Classical

namespace SymmetricSubgroupAsymptotics.CFSGTwistedAUnitaryCoordinates
open CFSGTwistedAUpperUnipotent

abbrev rankTwoUpperImage (q : CFSG.PrimePower) (hq : 3 ≤ q.order) :=
  (rankTwoUpperSubgroup q).map (rankTwoProjectiveCover q hq)

abbrev rankTwoOppositeImage (q : CFSG.PrimePower) (hq : 3 ≤ q.order) :=
  (rankTwoOppositeSubgroup q).map (rankTwoProjectiveCover q hq)

private theorem map_mul_automorphism {G : Type*} [Group G]
    (H : Subgroup G) (f g : MulAut G) :
    H.map (f * g).toMonoidHom = (H.map g.toMonoidHom).map f.toMonoidHom := by
  rw [Subgroup.map_map]
  rfl

private theorem map_inv_automorphism {G : Type*} [Group G]
    (H : Subgroup G) (f : MulAut G) (hf : H.map f.toMonoidHom = H) :
    H.map (f⁻¹).toMonoidHom = H := by
  have he : (H.map f.toMonoidHom).map (f⁻¹).toMonoidHom = H := by
    rw [Subgroup.map_map]
    have hh : (f⁻¹).toMonoidHom.comp f.toMonoidHom = MonoidHom.id G := by
      ext x
      exact f.symm_apply_apply x
    rw [hh, Subgroup.map_id]
  rwa [hf] at he

def rankTwoPairStabilizer (q : CFSG.PrimePower) (hq : 3 ≤ q.order) :
    Subgroup (MulAut (CFSG.Models.TwistedA 2 q)) where
  carrier := {f | (rankTwoUpperImage q hq).map f.toMonoidHom = rankTwoUpperImage q hq ∧
    (rankTwoOppositeImage q hq).map f.toMonoidHom = rankTwoOppositeImage q hq}
  one_mem' := by constructor <;> exact Subgroup.map_id _
  mul_mem' := by
    rintro f g ⟨hf, hf'⟩ ⟨hg, hg'⟩
    constructor
    · rw [map_mul_automorphism, hg, hf]
    · rw [map_mul_automorphism, hg', hf']
  inv_mem' := by
    rintro f ⟨hf, hf'⟩
    exact ⟨map_inv_automorphism _ f hf, map_inv_automorphism _ f hf'⟩

def rankTwo_restrictRadical (q : CFSG.PrimePower) (hq : 3 ≤ q.order)
    (f : MulAut (CFSG.Models.TwistedA 2 q))
    (hf : (rankTwoUpperImage q hq).map f.toMonoidHom = rankTwoUpperImage q hq) :
    MulAut (fixedRadical q 0) :=
  (rankTwoRadicalProjectiveEquiv q hq).trans
    (((f.subgroupMap (rankTwoUpperImage q hq)).trans (MulEquiv.subgroupCongr hf)).trans
      (rankTwoRadicalProjectiveEquiv q hq).symm)

theorem rankTwo_restrictRadical_intertwines (q : CFSG.PrimePower) (hq : 3 ≤ q.order)
    (f : MulAut (CFSG.Models.TwistedA 2 q))
    (hf : (rankTwoUpperImage q hq).map f.toMonoidHom = rankTwoUpperImage q hq)
    (r : fixedRadical q 0) :
    (rankTwoRadicalProjectiveEquiv q hq (rankTwo_restrictRadical q hq f hf r)).val =
      f (rankTwoRadicalProjectiveEquiv q hq r).val := by
  let e := rankTwoRadicalProjectiveEquiv q hq
  change (e (e.symm (((f.subgroupMap (rankTwoUpperImage q hq)).trans
    (MulEquiv.subgroupCongr hf)) (e r)))).val = _
  rw [e.apply_symm_apply]
  rfl

def rankTwoPairRestriction (q : CFSG.PrimePower) (hq : 3 ≤ q.order) :
    rankTwoPairStabilizer q hq →* MulAut (fixedRadical q 0) where
  toFun f := rankTwo_restrictRadical q hq f.val f.property.1
  map_one' := by
    apply MulEquiv.ext
    intro r
    apply (rankTwoRadicalProjectiveEquiv q hq).injective
    apply Subtype.ext
    change (rankTwoRadicalProjectiveEquiv q hq
      (rankTwo_restrictRadical q hq 1 _ r)).val = (rankTwoRadicalProjectiveEquiv q hq r).val
    rw [rankTwo_restrictRadical_intertwines]
    rfl
  map_mul' f g := by
    apply MulEquiv.ext
    intro r
    apply (rankTwoRadicalProjectiveEquiv q hq).injective
    apply Subtype.ext
    change (rankTwoRadicalProjectiveEquiv q hq
      (rankTwo_restrictRadical q hq (f.val * g.val) _ r)).val =
      (rankTwoRadicalProjectiveEquiv q hq (rankTwo_restrictRadical q hq f.val f.property.1
        (rankTwo_restrictRadical q hq g.val g.property.1 r))).val
    simp only [rankTwo_restrictRadical_intertwines]
    rfl

theorem rankTwoPairRestriction_injective (q : CFSG.PrimePower) (hq : 3 ≤ q.order)
    [IsSimpleGroup (CFSG.Models.TwistedA 2 q)] : Function.Injective (rankTwoPairRestriction q hq) := by
  apply (rankTwoPairRestriction q hq).ker_eq_bot_iff.mp
  apply bot_unique
  intro f hf
  apply Subgroup.mem_bot.mpr
  apply Subtype.ext
  apply rankTwo_eq_one_of_fixed_radical_pair q hq f.val f.property.1 f.property.2
  intro u
  obtain ⟨r, rfl⟩ := (rankTwoRadicalProjectiveEquiv q hq).surjective u
  have he := congrArg (fun A : MulAut (fixedRadical q 0) =>
    (rankTwoRadicalProjectiveEquiv q hq (A r)).val) hf
  change (rankTwoRadicalProjectiveEquiv q hq
    (rankTwo_restrictRadical q hq f.val f.property.1 r)).val =
      (rankTwoRadicalProjectiveEquiv q hq r).val at he
  rwa [rankTwo_restrictRadical_intertwines] at he

end SymmetricSubgroupAsymptotics.CFSGTwistedAUnitaryCoordinates
