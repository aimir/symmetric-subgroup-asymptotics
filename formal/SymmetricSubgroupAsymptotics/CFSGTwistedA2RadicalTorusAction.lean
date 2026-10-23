import SymmetricSubgroupAsymptotics.CFSGTwistedA2RadicalFirstLayer
import SymmetricSubgroupAsymptotics.CFSGTwistedA2HeisenbergCentralAction
import SymmetricSubgroupAsymptotics.CFSGTwistedAUnitaryRadicalUpperEmbedding
import SymmetricSubgroupAsymptotics.CFSGUnitaryRankTwoWeightField
import Mathlib.Tactic.Group

/-! Literal rank-two torus action on the SAME radical and its intrinsic
quotient. The vector parameter is entry(1,2), hence its multiplier is
sigma(firstWeight z); the older first array parameter is entry(0,1).
No sign or parameter identification is silently substituted. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Matrix

namespace SymmetricSubgroupAsymptotics.CFSGTwistedAUnitaryCoordinates
open CFSGTwistedANaturalMatrices CFSGTwistedAUpperUnipotent
open CFSGTwistedAUnitaryNaturalRadical CFSGSerreOrdinaryTwists
open CFSGTwistedA2DiagonalTorus

theorem rankTwo_upper_mem_radical (q : CFSG.PrimePower) (u : naturalUnipotent 2 q) :
    upperFixedHom q 2 u ∈ fixedRadical q 0 := by
  apply (mem_fixedRadical_iff_natural_support q 0 _).mpr
  refine ⟨u.property.1.2, ?_⟩
  intro i j hi hj
  change (u.val.val : Mat (q.Extension 2) 2) i j = (1 : Mat (q.Extension 2) 2) i j
  by_cases hij : i = j
  · subst j
    exact (u.property.1.2 i).trans (Matrix.one_apply_eq i).symm
  · rw [Matrix.one_apply, if_neg hij]
    have hi0 : i.val ≠ 0 := fun h => hi (Fin.ext h)
    have hj2 : j.val ≠ 2 := fun h => hj (Fin.ext h)
    have hji : j < i := by
      change j.val < i.val
      have hival := i.isLt
      have hjval := j.isLt
      have hne : i.val ≠ j.val := fun h => hij (Fin.ext h)
      omega
    exact u.property.1.1 hji

theorem rankTwoParameterHom_entry (q : CFSG.PrimePower) (g : fixedRadical q 0) :
    (rankTwoParameterHom q g).toAdd = (g.val.val.val : Mat (q.Extension 2) 2) 1 2 := by
  change (blockFixedMatrixHom q 0 g.val :
    Matrix (CFSGTwistedAUnitaryUpperArrays.Index (Fin 1))
      (CFSGTwistedAUnitaryUpperArrays.Index (Fin 1)) (q.Extension 2))
      (.inr (.inl 0)) (.inr (.inr ())) = _
  exact blockFixedMatrixHom_apply q 0 g.val (.inr (.inl 0)) (.inr (.inr ()))

theorem rankTwoTorus_conjugate_entry (q : CFSG.PrimePower) (z : (q.Extension 2)ˣ)
    (g : naturalFixed 2 q) (i j : Fin 3) :
    (((rankTwoNaturalTorus q z * g * (rankTwoNaturalTorus q z)⁻¹).val.val :
      Mat (q.Extension 2) 2) i j) =
      torusWeights (q.Extension 2) (definingFieldAutomorphism q 2) z i *
      (g.val.val : Mat (q.Extension 2) 2) i j *
      torusWeights (q.Extension 2) (definingFieldAutomorphism q 2) (z⁻¹ : (q.Extension 2)ˣ) j := by
  rw [← map_inv (rankTwoNaturalTorus q) z]
  change (((rankTwoNaturalTorus q z).val.val : Mat (q.Extension 2) 2) *
    (g.val.val : Mat (q.Extension 2) 2) *
    ((rankTwoNaturalTorus q z⁻¹).val.val : Mat (q.Extension 2) 2)) i j = _
  rw [rankTwoNaturalTorus_matrix, rankTwoNaturalTorus_matrix,
    Matrix.mul_diagonal, Matrix.diagonal_mul]

theorem rankTwo_torusWeights_inv_mul (q : CFSG.PrimePower) (z : (q.Extension 2)ˣ)
    (i : Fin 3) :
    torusWeights (q.Extension 2) (definingFieldAutomorphism q 2) z i *
      torusWeights (q.Extension 2) (definingFieldAutomorphism q 2) (z⁻¹ : (q.Extension 2)ˣ) i = 1 := by
  fin_cases i <;> simp [torusWeights, Units.val_inv_eq_inv_val, map_inv₀]
  all_goals field_simp [Units.ne_zero z,
    (map_ne_zero (definingFieldAutomorphism q 2)).mpr (Units.ne_zero z)]

theorem rankTwoTorus_conjugate_mem_radical (q : CFSG.PrimePower) (z : (q.Extension 2)ˣ)
    (g : fixedRadical q 0) :
    rankTwoNaturalTorus q z * g.val * (rankTwoNaturalTorus q z)⁻¹ ∈ fixedRadical q 0 := by
  let v := rankTwoNaturalTorus q z * g.val * (rankTwoNaturalTorus q z)⁻¹
  have hg := fixedRadical_mem_upper q 0 g
  have hv : v.val ∈ naturalUnipotent 2 q := by
    refine ⟨⟨?_, ?_⟩, v.property⟩
    · intro i j hij
      change (v.val.val : Mat (q.Extension 2) 2) i j = 0
      have hz := hg.1.1 hij
      change (g.val.val.val : Mat (q.Extension 2) 2) i j = 0 at hz
      rw [rankTwoTorus_conjugate_entry, hz, mul_zero, zero_mul]
    · intro i
      change (v.val.val : Mat (q.Extension 2) 2) i i = 1
      have hd := hg.1.2 i
      change (g.val.val.val : Mat (q.Extension 2) 2) i i = 1 at hd
      rw [rankTwoTorus_conjugate_entry, hd, mul_one, rankTwo_torusWeights_inv_mul]
  exact rankTwo_upper_mem_radical q ⟨v.val, hv⟩

def rankTwoRadicalTorusEnd (q : CFSG.PrimePower) (z : (q.Extension 2)ˣ) :
    fixedRadical q 0 →* fixedRadical q 0 where
  toFun g := ⟨rankTwoNaturalTorus q z * g.val * (rankTwoNaturalTorus q z)⁻¹,
    rankTwoTorus_conjugate_mem_radical q z g⟩
  map_one' := by
    apply Subtype.ext
    change rankTwoNaturalTorus q z * (1 : naturalFixed 2 q) * (rankTwoNaturalTorus q z)⁻¹ = 1
    group
  map_mul' g h := by
    apply Subtype.ext
    change rankTwoNaturalTorus q z * (g.val * h.val) * (rankTwoNaturalTorus q z)⁻¹ =
      (rankTwoNaturalTorus q z * g.val * (rankTwoNaturalTorus q z)⁻¹) *
      (rankTwoNaturalTorus q z * h.val * (rankTwoNaturalTorus q z)⁻¹)
    group

def rankTwoRadicalTorusAut (q : CFSG.PrimePower) (z : (q.Extension 2)ˣ) :
    MulAut (fixedRadical q 0) :=
  MulEquiv.ofBijective (rankTwoRadicalTorusEnd q z) (by
    constructor
    · intro g h he
      apply Subtype.ext
      exact (MulAut.conj (rankTwoNaturalTorus q z)).injective (congrArg Subtype.val he)
    · intro g
      refine ⟨rankTwoRadicalTorusEnd q z⁻¹ g, ?_⟩
      apply Subtype.ext
      change rankTwoNaturalTorus q z *
        (rankTwoNaturalTorus q z⁻¹ * g.val * (rankTwoNaturalTorus q z⁻¹)⁻¹) *
        (rankTwoNaturalTorus q z)⁻¹ = g.val
      rw [map_inv]
      group)

def rankTwoRadicalTorusAutHom (q : CFSG.PrimePower) :
    (q.Extension 2)ˣ →* MulAut (fixedRadical q 0) where
  toFun := rankTwoRadicalTorusAut q
  map_one' := by
    apply MulEquiv.ext
    intro g
    apply Subtype.ext
    change rankTwoNaturalTorus q 1 * g.val * (rankTwoNaturalTorus q 1)⁻¹ = g.val
    rw [map_one]
    group
  map_mul' z w := by
    apply MulEquiv.ext
    intro g
    apply Subtype.ext
    change rankTwoNaturalTorus q (z * w) * g.val * (rankTwoNaturalTorus q (z * w))⁻¹ =
      rankTwoNaturalTorus q z * (rankTwoNaturalTorus q w * g.val *
        (rankTwoNaturalTorus q w)⁻¹) * (rankTwoNaturalTorus q z)⁻¹
    rw [map_mul]
    group

theorem rankTwoRadicalTorusAut_first (q : CFSG.PrimePower) (z : (q.Extension 2)ˣ)
    (g : fixedRadical q 0) :
    (rankTwoParameterHom q (rankTwoRadicalTorusAut q z g)).toAdd =
      definingFieldAutomorphism q 2
        (firstWeight (q.Extension 2) (definingFieldAutomorphism q 2) (z : q.Extension 2)) *
        (rankTwoParameterHom q g).toAdd := by
  rw [rankTwoParameterHom_entry, rankTwoParameterHom_entry]
  change (((rankTwoNaturalTorus q z * g.val * (rankTwoNaturalTorus q z)⁻¹).val.val :
    Mat (q.Extension 2) 2) 1 2) = _
  rw [rankTwoTorus_conjugate_entry]
  have htwice : definingFieldAutomorphism q 2 (definingFieldAutomorphism q 2 (z : q.Extension 2)) =
      (z : q.Extension 2) := extension_two_pow_twice q z
  have hw1 : torusWeights (q.Extension 2) (definingFieldAutomorphism q 2) (z : q.Extension 2) (1 : Fin 3) =
      definingFieldAutomorphism q 2 z / (z : q.Extension 2) := rfl
  have hw2 : torusWeights (q.Extension 2) (definingFieldAutomorphism q 2)
      (z⁻¹ : (q.Extension 2)ˣ) (2 : Fin 3) =
      (definingFieldAutomorphism q 2 (z⁻¹ : (q.Extension 2)ˣ))⁻¹ := rfl
  rw [hw1, hw2, Units.val_inv_eq_inv_val]
  dsimp only [firstWeight]
  rw [map_inv₀, inv_inv, map_div₀, map_pow, htwice]
  field_simp [Units.ne_zero z, (map_ne_zero (definingFieldAutomorphism q 2)).mpr (Units.ne_zero z)]

theorem rankTwoRadicalTorusAut_centre_of_norm_one (q : CFSG.PrimePower)
    (z : (q.Extension 2)ˣ)
    (hz : (z : q.Extension 2) * definingFieldAutomorphism q 2 z = 1)
    (c : Multiplicative (centralParameters q 0)) :
    rankTwoRadicalTorusAut q z (centralRadicalHom q 0 c) = centralRadicalHom q 0 c := by
  apply Subtype.ext
  change rankTwoNaturalTorus q z * centralFixed q 0 c.toAdd.val
    (centralParameters_condition q 0 c.toAdd.val c.toAdd.property) * (rankTwoNaturalTorus q z)⁻¹ =
    centralFixed q 0 c.toAdd.val (centralParameters_condition q 0 c.toAdd.val c.toAdd.property)
  simpa only [hz, one_mul] using rankTwoNaturalTorus_centralFixed_conjugation q z c.toAdd.val
    (centralParameters_condition q 0 c.toAdd.val c.toAdd.property)

end SymmetricSubgroupAsymptotics.CFSGTwistedAUnitaryCoordinates
