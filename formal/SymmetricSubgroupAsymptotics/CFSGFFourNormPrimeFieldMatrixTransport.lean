import SymmetricSubgroupAsymptotics.CFSGFFourNormSparseWordMatrix

/-! One-way original-word equality and commutation transfer to the SAME
prime-field norm matrix. No faithfulness of the norm representation is
assumed: coefficient-ring injectivity alone transfers the equality. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGFFourNormPrimeFieldMatrixTransport
open CFSGFFourNormPrimeFieldWords CFSGFFourNormSparseWordMatrix

variable (K : Type) [_root_.Field K] [Finite K] [CharP K 2]

theorem evaluate_eq_of_wordValue_eq (s t : List Letter)
    (h : wordValue K s=wordValue K t) (v : Fin 26 → ZMod 2) :
    evaluate (ZMod 2) s v=evaluate (ZMod 2) t v := by
  let e : ZMod 2 →+* K := ZMod.castHom (dvd_refl 2) K
  have hk : evaluate K s (fun j => e (v j))=evaluate K t (fun j => e (v j)) := by
    rw [←wordValue_action K s (fun j => e (v j)),
      ←wordValue_action K t (fun j => e (v j)),h]
  funext j
  apply e.injective
  exact (congrFun (evaluate_map (ZMod 2) K e s v) j).trans
    ((congrFun hk j).trans (congrFun (evaluate_map (ZMod 2) K e t v) j).symm)

theorem wordMatrix_eq_of_wordValue_eq (s t : List Letter)
    (h : wordValue K s=wordValue K t) :
    wordMatrix (ZMod 2) s=wordMatrix (ZMod 2) t := by
  apply Matrix.ext
  intro i j
  rw [←evaluate_basis_entry,←evaluate_basis_entry]
  exact congrFun (evaluate_eq_of_wordValue_eq K s t h
    (fun k => if k=j then 1 else 0)) i

theorem wordMatrix_commute_of_wordValue_commute (s t : List Letter)
    (h : Commute (wordValue K s) (wordValue K t)) :
    Commute (wordMatrix (ZMod 2) s) (wordMatrix (ZMod 2) t) := by
  have hw : wordValue K (s++t)=wordValue K (t++s) := by
    rw [wordValue_append,wordValue_append]
    exact h.eq
  have hm := wordMatrix_eq_of_wordValue_eq K (s++t) (t++s) hw
  change wordMatrix (ZMod 2) s*wordMatrix (ZMod 2) t=
    wordMatrix (ZMod 2) t*wordMatrix (ZMod 2) s
  simpa only [wordMatrix_append] using hm

end SymmetricSubgroupAsymptotics.CFSGFFourNormPrimeFieldMatrixTransport
