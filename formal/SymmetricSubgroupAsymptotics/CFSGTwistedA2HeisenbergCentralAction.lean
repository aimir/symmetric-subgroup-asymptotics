import SymmetricSubgroupAsymptotics.CFSGUnitaryRankTwoTorus
import SymmetricSubgroupAsymptotics.CFSGTwistedAUnitaryCentralNormOrbit

/-! Rank-two central norm conjugacy in the SAME original fixed-derived
source. The full quadratic-field torus supplies the norm multiplier;
no named unitary-group identification is used. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section

namespace SymmetricSubgroupAsymptotics.CFSGTwistedAUnitaryCoordinates
open CFSGTwistedANaturalMatrices CFSGTwistedAUpperUnipotent
open CFSGSerreOrdinaryTwists CFSGTwistedAUnitaryNaturalRadical
open CFSGTwistedA2UnipotentArrays CFSGTwistedA2DiagonalTorus

theorem rankTwoNaturalTorus_centralFixed_conjugation (q : CFSG.PrimePower)
    (a : (q.Extension 2)ˣ) (b : q.Extension 2) (hb : Condition q 0 0 b) :
    rankTwoNaturalTorus q a * centralFixed q 0 b hb * (rankTwoNaturalTorus q a)⁻¹ =
      centralFixed q 0 ((a : q.Extension 2) * definingFieldAutomorphism q 2 a * b)
        (centralParameter_norm_mul_condition q 0 a b hb) := by
  let g := rankTwoNaturalTorus q a
  have hcol (i : Fin 3) : (g.val.val : Mat (q.Extension 2) 2) i 0 =
      if i = 0 then (a : q.Extension 2) else 0 := by
    rw [rankTwoNaturalTorus_matrix]
    fin_cases i <;> simp [torusWeights, Matrix.diagonal]
  have hform := fixed_unit_signedForm (q.Extension 2) 2
    (definingFieldAutomorphism q 2).toRingHom g.val.val g.property
  change ((g.val.val : Mat (q.Extension 2) 2).map (definingFieldAutomorphism q 2)).transpose *
    (signedReversalUnit (q.Extension 2) 2 : Mat (q.Extension 2) 2) *
    (g.val.val : Mat (q.Extension 2) 2) = _ at hform
  apply Subtype.ext
  apply Subtype.ext
  apply Units.ext
  change (g.val.val : Mat (q.Extension 2) 2) *
    ((centralFixed q 0 b hb).val.val : Mat (q.Extension 2) 2) *
    (((g.val.val)⁻¹ : (Mat (q.Extension 2) 2)ˣ) : Mat (q.Extension 2) 2) =
    ((centralFixed q 0 ((a : q.Extension 2) * definingFieldAutomorphism q 2 a * b)
      (centralParameter_norm_mul_condition q 0 a b hb)).val.val : Mat (q.Extension 2) 2)
  rw [show ((centralFixed q 0 b hb).val.val : Mat (q.Extension 2) 2) =
      1 + Matrix.single (0 : Fin 3) (Fin.last 2) b from radicalCentral_matrix q 0 b hb]
  rw [show ((centralFixed q 0 ((a : q.Extension 2) * definingFieldAutomorphism q 2 a * b)
      (centralParameter_norm_mul_condition q 0 a b hb)).val.val : Mat (q.Extension 2) 2) =
      1 + Matrix.single (0 : Fin 3) (Fin.last 2)
        ((a : q.Extension 2) * definingFieldAutomorphism q 2 a * b) from
    radicalCentral_matrix q 0 _ (centralParameter_norm_mul_condition q 0 a b hb)]
  exact extreme_single_conjugation 2 (definingFieldAutomorphism q 2) g.val.val a b hform hcol

theorem rankTwo_exists_conjugate_centralFixed (q : CFSG.PrimePower)
    (b c : q.Extension 2) (hb : Condition q 0 0 b) (hc : Condition q 0 0 c)
    (hb0 : b ≠ 0) (hc0 : c ≠ 0) :
    ∃ g : naturalFixed 2 q, g * centralFixed q 0 b hb * g⁻¹ = centralFixed q 0 c hc := by
  have hbc : b ∈ centralParameters q 0 := (centralCondition_iff q 0 b).mp hb
  have hcc : c ∈ centralParameters q 0 := (centralCondition_iff q 0 c).mp hc
  have hratio : definingFieldAutomorphism q 2 (b⁻¹ * c) = b⁻¹ * c :=
    centralParameter_div_fixed q 0 b hb0 hbc ⟨c, hcc⟩
  obtain ⟨a, ha⟩ := exists_norm_eq_fixed q (b⁻¹ * c) hratio
  have ha0 : a ≠ 0 := by
    intro he
    apply mul_ne_zero (inv_ne_zero hb0) hc0
    calc
      b⁻¹ * c = a * definingFieldAutomorphism q 2 a := ha.symm
      _ = 0 := by rw [he, zero_mul]
  have hab : a * definingFieldAutomorphism q 2 a * b = c := by
    rw [ha]
    field_simp [hb0]
  refine ⟨rankTwoNaturalTorus q (Units.mk0 a ha0), ?_⟩
  simpa only [Units.val_mk0, hab] using
    rankTwoNaturalTorus_centralFixed_conjugation q (Units.mk0 a ha0) b hb

def rankTwoRadicalHom (q : CFSG.PrimePower) (hq : 3 ≤ q.order) :
    fixedRadical q 0 →* CFSG.Models.TwistedA 2 q :=
  (rankTwoProjectiveCover q hq).comp (fixedRadical q 0).subtype

def rankTwoCentralParameterHom (q : CFSG.PrimePower) (hq : 3 ≤ q.order) :
    Multiplicative (centralParameters q 0) →* CFSG.Models.TwistedA 2 q :=
  (rankTwoRadicalHom q hq).comp (centralRadicalHom q 0)

theorem rankTwoCentralParameter_conjugate (q : CFSG.PrimePower) (hq : 3 ≤ q.order)
    (x y : Multiplicative (centralParameters q 0)) (hx : x ≠ 1) (hy : y ≠ 1) :
    ∃ g : CFSG.Models.TwistedA 2 q,
      g * rankTwoCentralParameterHom q hq x * g⁻¹ = rankTwoCentralParameterHom q hq y := by
  have hx0 : x.toAdd.val ≠ 0 := by
    intro he
    exact hx (Multiplicative.toAdd.injective (Subtype.ext he))
  have hy0 : y.toAdd.val ≠ 0 := by
    intro he
    exact hy (Multiplicative.toAdd.injective (Subtype.ext he))
  obtain ⟨g, hg⟩ := rankTwo_exists_conjugate_centralFixed q x.toAdd.val y.toAdd.val
    (centralParameters_condition q 0 x.toAdd.val x.toAdd.property)
    (centralParameters_condition q 0 y.toAdd.val y.toAdd.property) hx0 hy0
  refine ⟨rankTwoProjectiveCover q hq g, ?_⟩
  change rankTwoProjectiveCover q hq g *
    rankTwoProjectiveCover q hq (centralFixed q 0 x.toAdd.val
      (centralParameters_condition q 0 x.toAdd.val x.toAdd.property)) *
    (rankTwoProjectiveCover q hq g)⁻¹ =
    rankTwoProjectiveCover q hq (centralFixed q 0 y.toAdd.val
      (centralParameters_condition q 0 y.toAdd.val y.toAdd.property))
  simpa only [map_mul, map_inv] using congrArg (rankTwoProjectiveCover q hq) hg

end SymmetricSubgroupAsymptotics.CFSGTwistedAUnitaryCoordinates
