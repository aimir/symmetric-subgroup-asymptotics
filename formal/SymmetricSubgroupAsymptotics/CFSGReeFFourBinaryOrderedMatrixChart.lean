import SymmetricSubgroupAsymptotics.CFSGReeFFourBinaryOrderedAxisPowers
import SymmetricSubgroupAsymptotics.CFSGReeFFourBinaryOrderedBooleanParameters
import SymmetricSubgroupAsymptotics.CFSGReeFFourBinaryFirstGlobalEntry

/-! Exact original Boolean word to the literal twelve-factor matrix chart.
All inverse prefixes come from the same actual group words. The sole
finite interpolation is one or two Boolean bits on an arbitrary axis. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGReeFFourBinaryOrderedMatrixChart
open CFSGReeFFourBinaryOrderedAxisPowers CFSGReeFFourBinaryOrderedBooleanParameters
open CFSGReeFFourBinaryOrderedRootWords CFSGReeFFourBinaryOrderedMatrixData
open CFSGReeFFourBinaryFirstGlobalEntry CFSGFFourNormSparseWordMatrix
open MatrixBinaryAffineFactor

def bitValues (b : Fin 12 → Bool) : Fin 12 → ZMod 2 := fun i => if b i then 1 else 0

def axisPrefix (a : ℕ → ℕ) : ℕ → Mat
  | 0 => 1
  | n+1 => (if hn : n<8 then (axisMatrix ⟨n,hn⟩)^(a n) else 1)*axisPrefix a n

theorem ordered_matrix_prefix (m : ℕ) (a : ℕ → ℕ) (n : ℕ) (hn : n≤8) :
    wordMatrix (ZMod 2) (orderedLetters a n)=axisPrefix a n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    have hn8 : n<8 := Nat.lt_of_succ_le hn
    have hb := parameter_block_eq_axis_power m ⟨n,hn8⟩ (a n)
    change wordMatrix (ZMod 2) ((prefixLetters n).reverse++
      (List.replicate (a n) (baseLetters n)).flatten++prefixLetters n)=
      (axisMatrix ⟨n,hn8⟩)^(a n) at hb
    rw [orderedLetters,wordMatrix_append,hb,ih (Nat.le_of_succ_le hn)]
    rw [axisPrefix,dif_pos hn8]

private def productEight (f : Fin 8 → Mat) : Mat :=
  f 7*(f 6*(f 5*(f 4*(f 3*(f 2*(f 1*(f 0*1)))))))

private def productTwelve (f : Fin 12 → Mat) : Mat :=
  f 11*(f 10*(f 9*(f 8*(f 7*(f 6*(f 5*(f 4*(f 3*(f 2*(f 1*(f 0*1)))))))))))

private theorem axisPrefix_eight (a : ℕ → ℕ) :
    axisPrefix a 8=productEight (fun j => (axisMatrix j)^(a j.val)) := rfl

private theorem chart_product (b : Fin 12 → ZMod 2) :
    chartMatrix b=productTwelve (fun i => affineFactor (b i) (bitMatrix i)) := rfl

private theorem regroup (f : Fin 12 → Mat) (g : Fin 8 → Mat)
    (h0 : f 1*f 0=g 0) (h1 : f 2=g 1)
    (h2 : f 4*f 3=g 2) (h3 : f 5=g 3)
    (h4 : f 7*f 6=g 4) (h5 : f 8=g 5)
    (h6 : f 10*f 9=g 6) (h7 : f 11=g 7) :
    productTwelve f=productEight g := by
  simp only [productTwelve,productEight,←h0,←h1,←h2,←h3,←h4,←h5,←h6,←h7,
    Matrix.mul_assoc,Matrix.mul_one]

private theorem one_bit_power (b : Bool) (A : Mat) :
    affineFactor (if b then 1 else 0) A=A^b.toNat := by
  cases b <;> simp [affineFactor_zero,affineFactor_one]

theorem chart_boolean_blocks (b : Fin 12 → Bool) :
    chartMatrix (bitValues b)=
      productEight (fun j => (axisMatrix j)^(parameterExponents b j)) := by
  rw [chart_product]
  apply regroup
  · rw [congrFun bitMatrix_eq 1,congrFun bitMatrix_eq 0]
    change affineFactor (if b 1 then 1 else 0) (axisMatrix 0*axisMatrix 0)*
      affineFactor (if b 0 then 1 else 0) (axisMatrix 0)=
        (axisMatrix 0)^((b 0).toNat+2*(b 1).toNat)
    simpa only [pow_two] using two_bits_power (b 0) (b 1) (axisMatrix 0)
  · rw [congrFun bitMatrix_eq 2]
    exact one_bit_power (b 2) (axisMatrix 1)
  · rw [congrFun bitMatrix_eq 4,congrFun bitMatrix_eq 3]
    change affineFactor (if b 4 then 1 else 0) (axisMatrix 2*axisMatrix 2)*
      affineFactor (if b 3 then 1 else 0) (axisMatrix 2)=
        (axisMatrix 2)^((b 3).toNat+2*(b 4).toNat)
    simpa only [pow_two] using two_bits_power (b 3) (b 4) (axisMatrix 2)
  · rw [congrFun bitMatrix_eq 5]
    exact one_bit_power (b 5) (axisMatrix 3)
  · rw [congrFun bitMatrix_eq 7,congrFun bitMatrix_eq 6]
    change affineFactor (if b 7 then 1 else 0) (axisMatrix 4*axisMatrix 4)*
      affineFactor (if b 6 then 1 else 0) (axisMatrix 4)=
        (axisMatrix 4)^((b 6).toNat+2*(b 7).toNat)
    simpa only [pow_two] using two_bits_power (b 6) (b 7) (axisMatrix 4)
  · rw [congrFun bitMatrix_eq 8]
    exact one_bit_power (b 8) (axisMatrix 5)
  · rw [congrFun bitMatrix_eq 10,congrFun bitMatrix_eq 9]
    change affineFactor (if b 10 then 1 else 0) (axisMatrix 6*axisMatrix 6)*
      affineFactor (if b 9 then 1 else 0) (axisMatrix 6)=
        (axisMatrix 6)^((b 9).toNat+2*(b 10).toNat)
    simpa only [pow_two] using two_bits_power (b 9) (b 10) (axisMatrix 6)
  · rw [congrFun bitMatrix_eq 11]
    exact one_bit_power (b 11) (axisMatrix 7)

theorem encoded_word_matrix (b : Fin 12 → Bool) :
    wordMatrix (ZMod 2) (orderedLetters (exponentFunction b) 8)=
      chartMatrix (bitValues b) := by
  rw [ordered_matrix_prefix 0 (exponentFunction b) 8 (le_refl 8),axisPrefix_eight]
  have he : (fun j : Fin 8 => (axisMatrix j)^(exponentFunction b j.val))=
      (fun j : Fin 8 => (axisMatrix j)^(parameterExponents b j)) := by
    funext j
    simp only [exponentFunction,dif_pos j.isLt,Fin.eta]
  rw [he]
  exact (chart_boolean_blocks b).symm

end SymmetricSubgroupAsymptotics.CFSGReeFFourBinaryOrderedMatrixChart
