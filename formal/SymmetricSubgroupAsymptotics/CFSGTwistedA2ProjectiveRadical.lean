import SymmetricSubgroupAsymptotics.CFSGTwistedA2RadicalTorusAction
import SymmetricSubgroupAsymptotics.CFSGUnitaryRankTwoProjectiveNormalizer

/-! The SAME actual radical is isomorphic to the literal original
projective Sylow image. The upper/radical equality is proved by support,
and injection is inherited from the proved original central quotient
separation. Actual torus conjugation intertwines under this equivalence. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section

namespace SymmetricSubgroupAsymptotics.CFSGTwistedAUnitaryCoordinates
open CFSGTwistedAUpperUnipotent

theorem rankTwoRadical_eq_upperSubgroup (q : CFSG.PrimePower) :
    fixedRadical q 0 = rankTwoUpperSubgroup q := by
  ext g
  constructor
  · intro hg
    exact fixedRadical_mem_upper q 0 ⟨g, hg⟩
  · intro hg
    exact rankTwo_upper_mem_radical q ⟨g.val, hg⟩

def rankTwoRadicalToUpper (q : CFSG.PrimePower) :
    fixedRadical q 0 →* rankTwoUpperSubgroup q where
  toFun g := ⟨g.val, fixedRadical_mem_upper q 0 g⟩
  map_one' := Subtype.ext rfl
  map_mul' _ _ := Subtype.ext rfl

theorem rankTwoRadicalHom_injective (q : CFSG.PrimePower) (hq : 3 ≤ q.order) :
    Function.Injective (rankTwoRadicalHom q hq) := by
  intro x y he
  have he' : ((rankTwoProjectiveCover q hq).comp (rankTwoUpperSubgroup q).subtype)
      (rankTwoRadicalToUpper q x) =
    ((rankTwoProjectiveCover q hq).comp (rankTwoUpperSubgroup q).subtype)
      (rankTwoRadicalToUpper q y) := he
  have hh := rankTwoProjectiveUpper_injective q hq he'
  exact Subtype.ext (congrArg (fun u : rankTwoUpperSubgroup q => u.val) hh)

theorem rankTwoRadicalHom_range (q : CFSG.PrimePower) (hq : 3 ≤ q.order) :
    (rankTwoRadicalHom q hq).range =
      (rankTwoUpperSubgroup q).map (rankTwoProjectiveCover q hq) := by
  ext x
  constructor
  · rintro ⟨g, rfl⟩
    exact ⟨g.val, fixedRadical_mem_upper q 0 g, rfl⟩
  · rintro ⟨g, hg, rfl⟩
    exact ⟨⟨g, rankTwo_upper_mem_radical q ⟨g.val, hg⟩⟩, rfl⟩

def rankTwoRadicalProjectiveEquiv (q : CFSG.PrimePower) (hq : 3 ≤ q.order) :
    fixedRadical q 0 ≃* (rankTwoUpperSubgroup q).map (rankTwoProjectiveCover q hq) :=
  (MonoidHom.ofInjective (rankTwoRadicalHom_injective q hq)).trans
    (MulEquiv.subgroupCongr (rankTwoRadicalHom_range q hq))

theorem rankTwoRadicalProjectiveEquiv_apply (q : CFSG.PrimePower) (hq : 3 ≤ q.order)
    (g : fixedRadical q 0) :
    (rankTwoRadicalProjectiveEquiv q hq g).val = rankTwoRadicalHom q hq g := rfl

theorem rankTwoRadicalProjectiveEquiv_torus (q : CFSG.PrimePower) (hq : 3 ≤ q.order)
    (z : (q.Extension 2)ˣ) (g : fixedRadical q 0) :
    (rankTwoRadicalProjectiveEquiv q hq (rankTwoRadicalTorusAutHom q z g)).val =
      rankTwoProjectiveTorus q hq z * (rankTwoRadicalProjectiveEquiv q hq g).val *
        (rankTwoProjectiveTorus q hq z)⁻¹ := by
  change rankTwoProjectiveCover q hq
    (rankTwoNaturalTorus q z * g.val * (rankTwoNaturalTorus q z)⁻¹) =
      rankTwoProjectiveCover q hq (rankTwoNaturalTorus q z) *
        rankTwoProjectiveCover q hq g.val *
        (rankTwoProjectiveCover q hq (rankTwoNaturalTorus q z))⁻¹
  rw [map_mul, map_mul, map_inv]

end SymmetricSubgroupAsymptotics.CFSGTwistedAUnitaryCoordinates
