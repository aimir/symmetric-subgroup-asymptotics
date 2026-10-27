import SymmetricSubgroupAsymptotics.NatPolynomialDigitExtraction
import SymmetricSubgroupAsymptotics.KroneckerConvolutionCoefficientBound
import SymmetricSubgroupAsymptotics.MatrixNaturalRowDotReflection

/-! Kronecker-substitution dot reflection. One natural multiplication
replaces the per-coordinate arithmetic loop after separate literal
row/column bindings. The all-coefficient no-carry bound is proved from
n digit products, not assumed or restricted to the target coefficient. -/
set_option autoImplicit false
set_option Elab.async false
open scoped BigOperators Polynomial Matrix
namespace SymmetricSubgroupAsymptotics.MatrixKroneckerDotReflection
open KroneckerConvolutionCoefficientBound NatPolynomialDigitExtraction

def pack {n : ℕ} (B : ℕ) (r : Fin n → ℕ) : ℕ :=
  Nat.ofDigits B (List.ofFn r)

def reversePack {n : ℕ} (B : ℕ) (c : Fin n → ℕ) : ℕ :=
  pack B (fun i => c i.rev)

theorem pack_eq_sum {n : ℕ} (B : ℕ) (r : Fin n → ℕ) :
    pack B r=∑ i : Fin n, r i*B^i.val := by
  rw [pack,←eval_ofFn_eq_ofDigits,Polynomial.ofFn_eq_sum_monomial,
    Polynomial.eval_finsetSum]
  simp only [Polynomial.eval_monomial]

theorem reversePack_eq_sum {n : ℕ} (B : ℕ) (c : Fin n → ℕ) :
    reversePack B c=∑ i : Fin n, c i*B^(n-1-i.val) := by
  rw [reversePack,pack_eq_sum]
  simpa [Fin.revPerm,Fin.val_rev,Nat.sub_sub,Nat.add_comm] using
    (Equiv.sum_comp (Fin.revPerm : Equiv.Perm (Fin n))
      (fun i : Fin n => c i*B^i.rev.val))

/-- n=0 is intentionally excluded: n-1 would not select a dot coefficient. -/
theorem kronecker_dot {n p B : ℕ} (hn : 0<n) (r c : Fin n → ℕ)
    (hr : ∀ i, r i<p) (hc : ∀ i, c i<p) (hB : n*(p-1)^2<B) :
    ((pack B r*reversePack B c)/B^(n-1))%B=∑ i : Fin n, r i*c i := by
  have hBpos : 0<B := lt_of_le_of_lt (Nat.zero_le _) hB
  have hcoeff : ∀ k : ℕ,
      (Polynomial.ofFn n r*Polynomial.ofFn n (fun i => c i.rev)).coeff k<B :=
    fun k => (product_coeff_le r (fun i => c i.rev) hr (fun i => hc i.rev) k).trans_lt hB
  have he := eval_digit_eq_coeff
    (Polynomial.ofFn n r*Polynomial.ofFn n (fun i => c i.rev)) B hBpos hcoeff (n-1)
  rw [Polynomial.eval_mul,eval_ofFn_eq_ofDigits,eval_ofFn_eq_ofDigits] at he
  exact he.trans (middle_coeff_eq_dot hn r c)

/-- Cache bindings are separate from the one-multiplication arithmetic
certificate. No matrix entries or digit bounds are trusted data. -/
theorem selected_kronecker_row_dot_mod
    (p n B : ℕ) (hn : 0<n) (rows : Array String) (i z : Fin n)
    (row column : ℕ → ℕ) (R C target : ℕ)
    (hrow : ∀ j : Fin n, MatrixNaturalRowDotReflection.rawDigit rows i.val j.val=row j.val)
    (hcolumn : ∀ j : Fin n, MatrixNaturalRowDotReflection.rawDigit rows j.val z.val=column j.val)
    (hr : ∀ j : Fin n, row j.val<p) (hc : ∀ j : Fin n, column j.val<p)
    (hR : pack B (fun j : Fin n => row j.val)=R)
    (hC : reversePack B (fun j : Fin n => column j.val)=C)
    (hB : n*(p-1)^2<B)
    (hcheck : (((R*C)/B^(n-1))%B)%p=target%p) :
    (CFSG.Models.MatrixData.matrix p n rows *ᵥ
      (fun j => CFSG.Models.MatrixData.matrix p n rows j z)) i=(target : ZMod p) := by
  have he := kronecker_dot hn (fun j : Fin n => row j.val)
    (fun j : Fin n => column j.val) hr hc hB
  rw [hR,hC] at he
  apply MatrixNaturalRowDotReflection.selected_row_dot_mod p n rows i z
    row column target hrow hcolumn
  rw [MatrixNaturalRowDotReflection.natDot_eq_sum,←he]
  exact hcheck

/-- The natural digit cap q is independent of the field modulus p. -/
theorem selected_kronecker_row_dot_mod_of_digit_bound
    (p q n B : ℕ) (hn : 0<n) (rows : Array String) (i z : Fin n)
    (row column : ℕ → ℕ) (R C target : ℕ)
    (hrow : ∀ j : Fin n, MatrixNaturalRowDotReflection.rawDigit rows i.val j.val=row j.val)
    (hcolumn : ∀ j : Fin n, MatrixNaturalRowDotReflection.rawDigit rows j.val z.val=column j.val)
    (hr : ∀ j : Fin n, row j.val<q) (hc : ∀ j : Fin n, column j.val<q)
    (hR : pack B (fun j : Fin n => row j.val)=R)
    (hC : reversePack B (fun j : Fin n => column j.val)=C)
    (hB : n*(q-1)^2<B)
    (hcheck : (((R*C)/B^(n-1))%B)%p=target%p) :
    (CFSG.Models.MatrixData.matrix p n rows *ᵥ
      (fun j => CFSG.Models.MatrixData.matrix p n rows j z)) i=(target : ZMod p) := by
  have he := kronecker_dot hn (fun j : Fin n => row j.val)
    (fun j : Fin n => column j.val) hr hc hB
  rw [hR,hC] at he
  apply MatrixNaturalRowDotReflection.selected_row_dot_mod p n rows i z
    row column target hrow hcolumn
  rw [MatrixNaturalRowDotReflection.natDot_eq_sum,←he]
  exact hcheck


end SymmetricSubgroupAsymptotics.MatrixKroneckerDotReflection
