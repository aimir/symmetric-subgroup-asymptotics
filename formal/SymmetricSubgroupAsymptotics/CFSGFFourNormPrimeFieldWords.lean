import SymmetricSubgroupAsymptotics.CFSGFFourNormCertificateAction
import SymmetricSubgroupAsymptotics.CFSGFFourOriginalFoldedEquivalence

/-! Constant-parameter signed root words in the genuine original norm26
representation. Sparse evaluation commutes with every coefficient-ring map;
no finite action table, full word matrix, or group recognition is used. -/
set_option autoImplicit false
set_option Elab.async false
namespace SymmetricSubgroupAsymptotics.CFSGFFourNormPrimeFieldWords
open CFSGFFourNormCertificateAction CFSGFFourNormCertificateSparseAction
open CFSG.Models.Chevalley CFSGFFourOriginalFoldedEquivalence
open CFSGSerreModelRootGeneration CFSGFFourE6CharacteristicTwoNormImage

abbrev Letter := Bool × Fin 4

def evaluate (R : Type) [CommRing R] (s : List Letter) (v : Fin 26 → R) : Fin 26 → R :=
  s.foldr (fun x u => sparseStep R x.1 x.2 1 u) v

theorem evaluate_cons (R : Type) [CommRing R] (x : Letter) (s : List Letter)
    (v : Fin 26 → R) : evaluate R (x::s) v = sparseStep R x.1 x.2 1 (evaluate R s v) := rfl

theorem evaluate_append (R : Type) [CommRing R] (s t : List Letter) (v : Fin 26 → R) :
    evaluate R (s++t) v = evaluate R s (evaluate R t v) := by
  induction s with
  | nil => rfl
  | cons x s ih =>
    change sparseStep R x.1 x.2 1 (evaluate R (s++t) v) =
      sparseStep R x.1 x.2 1 (evaluate R s (evaluate R t v))
    rw [ih]

theorem evaluate_map (R K : Type) [CommRing R] [CommRing K] (e : R →+* K)
    (s : List Letter) (v : Fin 26 → R) :
    (fun j => e (evaluate R s v j)) = evaluate K s (fun j => e (v j)) := by
  induction s with
  | nil => rfl
  | cons x s ih =>
    change (fun j => e (sparseStep R x.1 x.2 1 (evaluate R s v) j)) =
      sparseStep K x.1 x.2 1 (evaluate K s (fun j => e (v j)))
    calc
      _ = sparseStep K x.1 x.2 1 (fun j => e (evaluate R s v j)) := by
        funext j
        simp only [sparseStep, map_add, map_mul, map_pow, map_sum, map_one]
      _ = _ := congrArg (sparseStep K x.1 x.2 1) ih

noncomputable section
private instance : DecidableEq (CFSGNormTwoRootPairing.Roots CartanMatrix.E₆) := Classical.decEq _

variable (K : Type) [Field K] [Finite K] [CharP K 2]

def wordValue (s : List Letter) : Model CartanMatrix.F₄ K :=
  (s.map (fun x => modelRoot CartanMatrix.F₄ K x.1 x.2 1)).prod

omit [Finite K] [CharP K 2] in
theorem wordValue_append (s t : List Letter) :
    wordValue K (s++t) = wordValue K s * wordValue K t := by
  simp only [wordValue, List.map_append, List.prod_append]

theorem wordValue_action (s : List Letter) (v : Fin 26 → K) :
    linearAction K (modelEquivFolded K (wordValue K s)) v = evaluate K s v := by
  induction s with
  | nil =>
    change linearAction K (modelEquivFolded K 1) v = v
    rw [map_one, map_one]
    rfl
  | cons x s ih =>
    change linearAction K (modelEquivFolded K
      (modelRoot CartanMatrix.F₄ K x.1 x.2 1 * wordValue K s)) v = _
    rw [map_mul, map_mul, modelEquivFolded_root, Module.End.mul_apply]
    change linearAction K (foldedRoot K x.1 x.2 1)
      (linearAction K (modelEquivFolded K (wordValue K s)) v) = _
    rw [linearAction_root_apply, ih]
    rfl

end
end SymmetricSubgroupAsymptotics.CFSGFFourNormPrimeFieldWords
