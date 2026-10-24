import SymmetricSubgroupAsymptotics.CFSGTwistedAQuadraticTrace
import Mathlib.LinearAlgebra.Span.Basic
import Mathlib.Tactic.FieldSimp

/-! Explicit signed fixed lines and paired coordinates in the actual
quadratic coefficient field.  Minus signs are retained in characteristic
two.  All cardinalities come from actual linear equivalences, rather
than a fixed-space dimension or fixed-quotient lifting assumption. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGQuadraticSignedFixedCoordinates
open CFSGSerreOrdinaryTwists CFSGTwistedANaturalMatrices
open CFSGTwistedA2FixedField CFSGTwistedAQuadraticTrace

def signedLine (q : CFSG.PrimePower) (eps : ℤ) :
    Submodule (fixedField q) (q.Extension 2) where
  carrier := {x | definingFieldAutomorphism q 2 x = (eps : q.Extension 2) * x}
  zero_mem' := by simp only [map_zero, mul_zero, Set.mem_setOf_eq]
  add_mem' ha hb := by
    change definingFieldAutomorphism q 2 (_ + _) = _
    rw [map_add, ha, hb, mul_add]
  smul_mem' c x hx := by
    have hc : definingFieldAutomorphism q 2 (c : q.Extension 2) = (c : q.Extension 2) :=
      c.property
    change definingFieldAutomorphism q 2 ((c : q.Extension 2) * x) =
      (eps : q.Extension 2) * ((c : q.Extension 2) * x)
    rw [map_mul, hc, hx]
    ring

theorem exists_signed_nonzero (q : CFSG.PrimePower) (eps : ℤ)
    (heps : eps = 1 ∨ eps = -1) :
    ∃ delta : signedLine q eps, delta.val ≠ 0 := by
  rcases heps with rfl | rfl
  · refine ⟨⟨1, ?_⟩, one_ne_zero⟩
    change definingFieldAutomorphism q 2 1 = ((1 : ℤ) : q.Extension 2) * 1
    simp
  · obtain ⟨t, ht, hs⟩ := exists_skew_nonzero q
    refine ⟨⟨t, ?_⟩, ht⟩
    change definingFieldAutomorphism q 2 t = ((-1 : ℤ) : q.Extension 2) * t
    simpa only [Int.cast_neg, Int.cast_one, neg_one_mul] using hs

def lineMap (q : CFSG.PrimePower) (eps : ℤ) (delta : signedLine q eps) :
    fixedField q →ₗ[fixedField q] signedLine q eps :=
  LinearMap.toSpanSingleton (fixedField q) (signedLine q eps) delta

theorem lineMap_injective (q : CFSG.PrimePower) (eps : ℤ)
    (delta : signedLine q eps) (hdelta : delta.val ≠ 0) :
    Function.Injective (lineMap q eps delta) := by
  intro a b hab
  have hh := congrArg (fun z : signedLine q eps => z.val) hab
  change (a : q.Extension 2) * delta.val = (b : q.Extension 2) * delta.val at hh
  exact Subtype.ext (mul_right_cancel₀ hdelta hh)

theorem lineMap_surjective (q : CFSG.PrimePower) (eps : ℤ)
    (heps : eps = 1 ∨ eps = -1)
    (delta : signedLine q eps) (hdelta : delta.val ≠ 0) :
    Function.Surjective (lineMap q eps delta) := by
  intro x
  have he : (eps : q.Extension 2) ≠ 0 := by
    rcases heps with rfl | rfl <;> simp
  have hx : definingFieldAutomorphism q 2 x.val = (eps : q.Extension 2) * x.val :=
    x.property
  have hd : definingFieldAutomorphism q 2 delta.val =
      (eps : q.Extension 2) * delta.val := delta.property
  have hf : definingFieldAutomorphism q 2 (x.val / delta.val) = x.val / delta.val := by
    rw [map_div₀, hx, hd]
    field_simp [he, hdelta] <;> ring
  refine ⟨⟨x.val / delta.val, hf⟩, ?_⟩
  apply Subtype.ext
  change (x.val / delta.val) * delta.val = x.val
  exact div_mul_cancel₀ x.val hdelta

def lineEquiv (q : CFSG.PrimePower) (eps : ℤ) (heps : eps = 1 ∨ eps = -1)
    (delta : signedLine q eps) (hdelta : delta.val ≠ 0) :
    fixedField q ≃ₗ[fixedField q] signedLine q eps :=
  LinearEquiv.ofBijective (lineMap q eps delta)
    ⟨lineMap_injective q eps delta hdelta, lineMap_surjective q eps heps delta hdelta⟩

theorem signedLine_card (q : CFSG.PrimePower) (eps : ℤ)
    (heps : eps = 1 ∨ eps = -1) : Nat.card (signedLine q eps) = q.order := by
  obtain ⟨delta, hd⟩ := exists_signed_nonzero q eps heps
  exact (Nat.card_congr (lineEquiv q eps heps delta hd).toEquiv).symm.trans
    (fixedField_card q)

def pairedSpace (q : CFSG.PrimePower) (eps : ℤ) :
    Submodule (fixedField q) ((q.Extension 2) × (q.Extension 2)) where
  carrier := {x | x.2 = (eps : q.Extension 2) * definingFieldAutomorphism q 2 x.1}
  zero_mem' := by
    change (0 : q.Extension 2) = (eps : q.Extension 2) * definingFieldAutomorphism q 2 0
    rw [map_zero, mul_zero]
  add_mem' ha hb := by
    change _ + _ = (eps : q.Extension 2) * definingFieldAutomorphism q 2 (_ + _)
    rw [ha, hb, map_add, mul_add]
  smul_mem' c x hx := by
    have hc : definingFieldAutomorphism q 2 (c : q.Extension 2) = (c : q.Extension 2) :=
      c.property
    change (c : q.Extension 2) * x.2 =
      (eps : q.Extension 2) * definingFieldAutomorphism q 2 ((c : q.Extension 2) * x.1)
    rw [hx, map_mul, hc]
    ring

def pairedEquiv (q : CFSG.PrimePower) (eps : ℤ) :
    (q.Extension 2) ≃ₗ[fixedField q] pairedSpace q eps where
  toFun t := ⟨(t, (eps : q.Extension 2) * definingFieldAutomorphism q 2 t), rfl⟩
  invFun x := x.val.1
  left_inv _ := rfl
  right_inv x := by
    apply Subtype.ext
    change (x.val.1, (eps : q.Extension 2) * definingFieldAutomorphism q 2 x.val.1) = x.val
    apply Prod.ext
    · rfl
    · exact x.property.symm
  map_add' a b := by
    apply Subtype.ext
    change (a + b, (eps : q.Extension 2) * definingFieldAutomorphism q 2 (a + b)) =
      (a + b, (eps : q.Extension 2) * definingFieldAutomorphism q 2 a +
        (eps : q.Extension 2) * definingFieldAutomorphism q 2 b)
    apply Prod.ext
    · rfl
    · rw [map_add, mul_add]
  map_smul' c a := by
    have hc : definingFieldAutomorphism q 2 (c : q.Extension 2) = (c : q.Extension 2) :=
      c.property
    apply Subtype.ext
    change ((c : q.Extension 2) * a,
        (eps : q.Extension 2) * definingFieldAutomorphism q 2 ((c : q.Extension 2) * a)) =
      ((c : q.Extension 2) * a,
        (c : q.Extension 2) * ((eps : q.Extension 2) * definingFieldAutomorphism q 2 a))
    apply Prod.ext
    · rfl
    · rw [map_mul, hc]
      ring

theorem pairedSpace_card (q : CFSG.PrimePower) (eps : ℤ) :
    Nat.card (pairedSpace q eps) = q.order ^ 2 :=
  (Nat.card_congr (pairedEquiv q eps).toEquiv).symm.trans (extension_two_card q)

end SymmetricSubgroupAsymptotics.CFSGQuadraticSignedFixedCoordinates
