import SymmetricSubgroupAsymptotics.CFSGFFourNormPrimeFieldWords

/-! A matrix for the SAME sparse word evaluation. Basis-column certificates
bind literal finite row data to arbitrary-vector action; no action table,
finite group enumeration or classification premise is involved. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGFFourNormSparseWordMatrix
open CFSGFFourNormPrimeFieldWords CFSGFFourNormCertificateSparseAction
open CFSGFFourNormCertificateRootOperators

variable (R : Type) [CommRing R]

def wordMatrix (s : List Letter) : Matrix (Fin 26) (Fin 26) R :=
  (s.map (fun x => rootOperator R x.1 x.2 1)).prod

theorem wordMatrix_append (s t : List Letter) :
    wordMatrix R (s++t)=wordMatrix R s*wordMatrix R t := by
  simp only [wordMatrix,List.map_append,List.prod_append]

variable [CharP R 2]

theorem evaluate_eq_mulVec (s : List Letter) (v : Fin 26 → R) :
    evaluate R s v=(wordMatrix R s).mulVec v := by
  induction s with
  | nil =>
    change v=(1 : Matrix (Fin 26) (Fin 26) R).mulVec v
    simp only [Matrix.one_mulVec]
  | cons x s ih =>
    change sparseStep R x.1 x.2 1 (evaluate R s v)=
      (rootOperator R x.1 x.2 1*wordMatrix R s).mulVec v
    rw [ih,sparseStep_eq_mulVec]
    exact Matrix.mulVec_mulVec v _ _

theorem evaluate_basis_entry (s : List Letter) (i j : Fin 26) :
    evaluate R s (fun k => if k=j then 1 else 0) i=wordMatrix R s i j := by
  have he : (fun k : Fin 26 => if k=j then (1 : R) else 0)=Pi.single j 1 := by
    funext k
    simp only [Pi.single_apply]
  rw [he,evaluate_eq_mulVec,Matrix.mulVec_single_one]
  rfl

theorem wordMatrix_eq_of_basis (s : List Letter)
    (M : Matrix (Fin 26) (Fin 26) R)
    (h : ∀i j : Fin 26,
      evaluate R s (fun k => if k=j then 1 else 0) i=M i j) :
    wordMatrix R s=M := by
  apply Matrix.ext
  intro i j
  exact (evaluate_basis_entry R s i j).symm.trans (h i j)

end SymmetricSubgroupAsymptotics.CFSGFFourNormSparseWordMatrix
