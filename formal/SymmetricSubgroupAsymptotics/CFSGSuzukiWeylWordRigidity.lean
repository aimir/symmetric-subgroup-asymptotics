import SymmetricSubgroupAsymptotics.CFSGSuzukiBruhatArray
import SymmetricSubgroupAsymptotics.CFSGSuzukiWeylWord
import SymmetricSubgroupAsymptotics.CFSGSuzukiWeylTorus

/-! Two original matrix entries show that W is the only element of its
torus coset satisfying the constant Weyl word with the original U fixed.
This is a symbolic four-dimensional calculation, with no group census. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Classical CharTwo
namespace SymmetricSubgroupAsymptotics.CFSGSuzukiBruhat
open CFSGSuzukiFieldParameters CFSGSuzukiUnipotent CFSGSuzukiTorus
variable {K : Type*} [Field K] [CharP K 2]

theorem twistedArray_mul_firstRow (t : K→+*K) (a b : K)
    (A : Matrix (Fin 4) (Fin 4) K) (j : Fin 4) :
    (twistedArray t a b*A) 0 j=A 0 j := by
  simp [Matrix.mul_apply,twistedArray,Fin.sum_univ_succ]

theorem weyl_word_entry01 (t : K→+*K) (l : K) :
    (twistedArray t 0 1*(reversingArray*twistedArray t l 0*reversingArray)*
      twistedArray t 1 1 : Matrix (Fin 4) (Fin 4) K) 0 1=l+l*t l := by
  rw [Matrix.mul_apply]
  simp only [twistedArray_mul_firstRow,mul_reversingArray_apply,reversingArray_mul_apply]
  simp [twistedArray,Fin.sum_univ_succ,Fin.rev]

theorem weyl_word_entry03 (t : K→+*K) (l : K) :
    (twistedArray t 0 1*(reversingArray*twistedArray t l 0*reversingArray)*
      twistedArray t 1 1 : Matrix (Fin 4) (Fin 4) K) 0 3=l^2*t l := by
  rw [Matrix.mul_apply]
  simp only [twistedArray_mul_firstRow,mul_reversingArray_apply,reversingArray_mul_apply]
  simp [twistedArray,Fin.sum_univ_succ,Fin.rev]

theorem weyl_torus_word_rigidity (m : ℕ) (c : (Field m)ˣ)
    (hword : weylElement m*normalizedTorusElement m c=
      unipotentElement m 0 1*
        ((weylElement m*normalizedTorusElement m c)*unipotentElement m 1 0*
          (weylElement m*normalizedTorusElement m c)⁻¹)*unipotentElement m 1 1) : c=1 := by
  let l : Field m := theta m (c : Field m)/(c : Field m)^2
  have hl : l≠0 := div_ne_zero (theta_ne_zero m (Units.ne_zero c)) (pow_ne_zero 2 (Units.ne_zero c))
  have hconj : (weylElement m*normalizedTorusElement m c)*unipotentElement m 1 0*
      (weylElement m*normalizedTorusElement m c)⁻¹=
        weylElement m*unipotentElement m l 0*weylElement m := by
    calc
      _=weylElement m*(normalizedTorusElement m c*unipotentElement m 1 0*
          (normalizedTorusElement m c)⁻¹)*(weylElement m)⁻¹ := by group
      _=weylElement m*unipotentElement m l 0*weylElement m := by
        rw [normalizedTorus_conjugation,weylElement_inv]
        simp only [mul_one,zero_div,l]
  rw [hconj] at hword
  have h01 := congrArg (fun g : CFSGSuzukiTorus.Ambient m =>
    (g : CFSG.Models.SuzukiConstruction.Mat m) 0 1) hword
  have h03 := congrArg (fun g : CFSGSuzukiTorus.Ambient m =>
    (g : CFSG.Models.SuzukiConstruction.Mat m) 0 3) hword
  have hright01 : ((unipotentElement m 0 1*(weylElement m*unipotentElement m l 0*weylElement m)*
      unipotentElement m 1 1 : CFSGSuzukiTorus.Ambient m) :
        CFSG.Models.SuzukiConstruction.Mat m) 0 1=l+l*theta m l := by
    exact weyl_word_entry01 (theta m) l
  have hright03 : ((unipotentElement m 0 1*(weylElement m*unipotentElement m l 0*weylElement m)*
      unipotentElement m 1 1 : CFSGSuzukiTorus.Ambient m) :
        CFSG.Models.SuzukiConstruction.Mat m) 0 3=l^2*theta m l := by
    exact weyl_word_entry03 (theta m) l
  dsimp only at h01 h03
  rw [hright01] at h01
  rw [hright03] at h03
  have hleft01 : ((weylElement m*normalizedTorusElement m c : CFSGSuzukiTorus.Ambient m) :
      CFSG.Models.SuzukiConstruction.Mat m) 0 1=0 := by
    change (CFSG.Models.SuzukiConstruction.weyl m*
      (normalizedTorusElement m c : CFSG.Models.SuzukiConstruction.Mat m)) 0 1=0
    rw [normalizedTorusElement_coe]
    change (reversingArray*diagonalTorus (theta m) (c : Field m) :
      Matrix (Fin 4) (Fin 4) (Field m)) 0 1=0
    rw [reversingArray_mul_apply]
    simp [diagonalTorus,Fin.rev]
  have hleft03 : ((weylElement m*normalizedTorusElement m c : CFSGSuzukiTorus.Ambient m) :
      CFSG.Models.SuzukiConstruction.Mat m) 0 3=(c : Field m)⁻¹ := by
    change (CFSG.Models.SuzukiConstruction.weyl m*
      (normalizedTorusElement m c : CFSG.Models.SuzukiConstruction.Mat m)) 0 3=(c : Field m)⁻¹
    rw [normalizedTorusElement_coe]
    change (reversingArray*diagonalTorus (theta m) (c : Field m) :
      Matrix (Fin 4) (Fin 4) (Field m)) 0 3=(c : Field m)⁻¹
    rw [reversingArray_mul_apply]
    simp [diagonalTorus,Fin.rev]
  rw [hleft01] at h01
  rw [hleft03] at h03
  have ht : theta m l=1 := by
    have he : l*theta m l=l := (CharTwo.add_eq_zero.mp h01.symm).symm
    exact mul_left_cancel₀ hl (he.trans (mul_one l).symm)
  have hl1 : l=1 := (theta m).injective (ht.trans (map_one (theta m)).symm)
  simp only [hl1,map_one,one_pow,mul_one] at h03
  apply Units.ext
  change (c : Field m)=1
  exact inv_eq_one.mp h03

end SymmetricSubgroupAsymptotics.CFSGSuzukiBruhat
