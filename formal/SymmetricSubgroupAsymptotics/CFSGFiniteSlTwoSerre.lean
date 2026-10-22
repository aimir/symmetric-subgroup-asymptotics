import Mathlib.Algebra.Lie.Sl2
import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import Mathlib.Tactic.Linarith

/-! The two Serre powers follow from actual finite-dimensional sl₂ data.
This is a representation theorem, not a recognition or source-faithfulness
assumption: a vector killed by the opposite root has the required string length. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGFiniteSlTwoSerre
variable {L : Type*} [LieRing L] [LieAlgebra ℚ L] [FiniteDimensional ℚ L]
    {h e f : L}

 theorem ad_pow_succ_eq_zero (t : IsSl2Triple h e f) (x : L) (n : ℕ)
    (hh : ⁅h,x⁆= -((n:ℚ) • x)) (hf : ⁅f,x⁆=0) :
    (LieAlgebra.ad ℚ L e^(n+1)) x=0 := by
  by_cases hx : x=0
  · subst x
    exact map_zero _
  · have hp : t.symm.HasPrimitiveVectorWith x (n:ℚ) :=
      { ne_zero := hx
        lie_h := by rw [neg_lie,hh,neg_neg]
        lie_e := hf }
    exact hp.pow_toEnd_f_eq_zero_of_eq_nat rfl

 theorem serre_of_integer_weight (t : IsSl2Triple h e f) (x : L) (a : ℤ)
    (ha : a≤0) (hh : ⁅h,x⁆=a • x) (hf : ⁅f,x⁆=0) :
    (LieAlgebra.ad ℚ L e^(-a).toNat) ⁅e,x⁆=0 := by
  have hm : ((-a).toNat:ℤ)= -a := Int.toNat_of_nonneg (neg_nonneg.mpr ha)
  have hcast : -(((-a).toNat:ℚ))=(a:ℚ) := by
    exact_mod_cast (show -(((-a).toNat:ℤ))=a by omega)
  have hh' : ⁅h,x⁆= -(((-a).toNat:ℚ) • x) := by
    rw [←neg_smul,hcast]
    simpa only [Int.cast_smul_eq_zsmul] using hh
  have hz := ad_pow_succ_eq_zero t x (-a).toNat hh' hf
  rw [pow_succ,Module.End.mul_apply] at hz
  exact hz

end SymmetricSubgroupAsymptotics.CFSGFiniteSlTwoSerre
