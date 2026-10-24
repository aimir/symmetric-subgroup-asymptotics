import SymmetricSubgroupAsymptotics.CFSGParabolicQuadricCount

/-! A common norm-level slice for split, odd-dimensional and nonsplit
orthogonal natural modules. The extra coordinates and their norm are
arbitrary. This is an exact vector count; no group orbit, transitivity,
proper-index bound or characteristic-prime factor is assumed. -/
set_option autoImplicit false
noncomputable section
open scoped BigOperators
namespace SymmetricSubgroupAsymptotics.HyperbolicNormLevelSliceCardinality
open CFSGParabolicQuadricCount
variable {K I W : Type} [Field K] [Fintype I] (Q : W → K) (a : K)

def LevelSlice :=
  {v : ((I → K) × W) × (I → K) //
    v.1.1 ≠ 0 ∧ dotDual v.1.1 v.2 + Q v.1.2 = a}

def sliceSigmaEquiv : LevelSlice (I := I) Q a ≃
    Σ x : {x : I → K // x ≠ 0}, Σ w : W,
      {y : I → K // dotDual x.val y = a-Q w} where
  toFun v := ⟨⟨v.val.1.1, v.property.1⟩, v.val.1.2,
    ⟨v.val.2, eq_sub_iff_add_eq.mpr v.property.2⟩⟩
  invFun p := ⟨((p.1.val, p.2.1), p.2.2.val), p.1.property,
    eq_sub_iff_add_eq.mp p.2.2.property⟩
  left_inv _ := rfl
  right_inv _ := rfl

/-- Every nonzero positive vector and every choice of extra coordinates
has exactly one affine dot-product fibre of cardinality q^(n-1). -/
theorem card_levelSlice [Finite K] [Finite W] :
    Nat.card (LevelSlice (I := I) Q a) =
      (Nat.card K^Fintype.card I-1)*Nat.card W*Nat.card K^(Fintype.card I-1) := by
  classical
  letI : Fintype K := Fintype.ofFinite K
  letI : Fintype W := Fintype.ofFinite W
  rw [Nat.card_congr (sliceSigmaEquiv (I := I) Q a)]
  have hf (x : {x : I → K // x ≠ 0}) (w : W) :
      Nat.card {y : I → K // dotDual x.val y = a-Q w} =
        Nat.card K^(Fintype.card I-1) := nonzero_dot_fibre_card x.val x.property _
  simp only [Nat.card_sigma]
  simp_rw [hf]
  simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  rw [← Nat.card_eq_fintype_card (α := W),
    ← Nat.card_eq_fintype_card (α := {x : I → K // x ≠ 0})]
  have hnonzero : Nat.card {x : I → K // x ≠ 0} = Nat.card K^Fintype.card I-1 := by
    have hcard : Nat.card {x : I → K // x ≠ 0} = Nat.card K^Nat.card I-1 := by
      simpa only [← Nat.card_eq_fintype_card, Nat.card_fun] using
        (Set.card_ne_eq (0 : I → K))
    simpa only [Nat.card_eq_fintype_card (α := I)] using hcard
  rw [hnonzero]
  exact (Nat.mul_assoc _ _ _).symm

end SymmetricSubgroupAsymptotics.HyperbolicNormLevelSliceCardinality
