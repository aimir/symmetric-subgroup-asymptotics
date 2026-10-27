import SymmetricSubgroupAsymptotics.MatrixKroneckerDotReflection

/-! Arbitrary reduced intermediate row, not just a literal source row.
The literal matrix column binding can be reused for every power stage. -/
set_option autoImplicit false
open scoped BigOperators Matrix
namespace SymmetricSubgroupAsymptotics.MatrixKroneckerRowStepReflection
open MatrixKroneckerDotReflection

theorem cast_dot_eq_of_check {n p B : ℕ} (hn : 0<n) (r c : Fin n → ℕ)
    (hr : ∀ i, r i<p) (hc : ∀ i, c i<p) (R C target : ℕ)
    (hR : pack B r=R) (hC : reversePack B c=C) (hB : n*(p-1)^2<B)
    (hcheck : (((R*C)/B^(n-1))%B)%p=target%p) :
    (∑ i : Fin n, (r i : ZMod p)*(c i : ZMod p))=(target : ZMod p) := by
  have he := kronecker_dot hn r c hr hc hB
  rw [hR,hC] at he
  have hm : ((∑ i : Fin n, r i*c i : ℕ) : ZMod p)=(target : ZMod p) :=
    (ZMod.natCast_eq_natCast_iff' _ _ p).mpr (by rw [←he]; exact hcheck)
  simpa only [Nat.cast_sum,Nat.cast_mul] using hm

theorem row_step_of_check {n p B : ℕ} (hn : 0<n) (rows : Array String)
    (z : Fin n) (v : Fin n → ZMod p) (r c : Fin n → ℕ)
    (hrow : ∀ i, v i=(r i : ZMod p))
    (hcolumn : ∀ i, MatrixNaturalRowDotReflection.rawDigit rows i.val z.val=c i)
    (hr : ∀ i, r i<p) (hc : ∀ i, c i<p) (R C target : ℕ)
    (hR : pack B r=R) (hC : reversePack B c=C) (hB : n*(p-1)^2<B)
    (hcheck : (((R*C)/B^(n-1))%B)%p=target%p) :
    (∑ i : Fin n, v i*CFSG.Models.MatrixData.matrix p n rows i z)=(target : ZMod p) := by
  calc
    _ = ∑ i : Fin n, (r i : ZMod p)*(c i : ZMod p) := by
      apply Finset.sum_congr rfl
      intro i _
      rw [hrow i]
      change (r i : ZMod p)*(MatrixNaturalRowDotReflection.rawDigit rows i.val z.val : ZMod p)=_
      rw [hcolumn i]
    _ = _ := cast_dot_eq_of_check hn r c hr hc R C target hR hC hB hcheck

/-- Natural digit bounds need not equal the ZMod modulus. -/
theorem cast_dot_eq_of_check_of_digit_bound {n p q B : ℕ} (hn : 0<n) (r c : Fin n → ℕ)
    (hr : ∀ i, r i<q) (hc : ∀ i, c i<q) (R C target : ℕ)
    (hR : pack B r=R) (hC : reversePack B c=C) (hB : n*(q-1)^2<B)
    (hcheck : (((R*C)/B^(n-1))%B)%p=target%p) :
    (∑ i : Fin n, (r i : ZMod p)*(c i : ZMod p))=(target : ZMod p) := by
  have he := kronecker_dot hn r c hr hc hB
  rw [hR,hC] at he
  have hm : ((∑ i : Fin n, r i*c i : ℕ) : ZMod p)=(target : ZMod p) :=
    (ZMod.natCast_eq_natCast_iff' _ _ p).mpr (by rw [←he]; exact hcheck)
  simpa only [Nat.cast_sum,Nat.cast_mul] using hm

theorem row_step_of_check_of_digit_bound {n p q B : ℕ} (hn : 0<n) (rows : Array String)
    (z : Fin n) (v : Fin n → ZMod p) (r c : Fin n → ℕ)
    (hrow : ∀ i, v i=(r i : ZMod p))
    (hcolumn : ∀ i, MatrixNaturalRowDotReflection.rawDigit rows i.val z.val=c i)
    (hr : ∀ i, r i<q) (hc : ∀ i, c i<q) (R C target : ℕ)
    (hR : pack B r=R) (hC : reversePack B c=C) (hB : n*(q-1)^2<B)
    (hcheck : (((R*C)/B^(n-1))%B)%p=target%p) :
    (∑ i : Fin n, v i*CFSG.Models.MatrixData.matrix p n rows i z)=(target : ZMod p) := by
  calc
    _ = ∑ i : Fin n, (r i : ZMod p)*(c i : ZMod p) := by
      apply Finset.sum_congr rfl
      intro i _
      rw [hrow i]
      change (r i : ZMod p)*(MatrixNaturalRowDotReflection.rawDigit rows i.val z.val : ZMod p)=_
      rw [hcolumn i]
    _ = _ := cast_dot_eq_of_check_of_digit_bound hn r c hr hc R C target hR hC hB hcheck


end SymmetricSubgroupAsymptotics.MatrixKroneckerRowStepReflection
