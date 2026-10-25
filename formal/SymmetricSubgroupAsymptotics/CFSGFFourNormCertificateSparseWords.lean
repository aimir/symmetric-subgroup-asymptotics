import SymmetricSubgroupAsymptotics.CFSGFFourNormCertificateSparseAction
import SymmetricSubgroupAsymptotics.CFSGReeFFourFieldEightWordTemplates
import Mathlib.Data.List.Fold

/-! Ordered sparse root words define genuine linear endomorphisms and
commute with a coefficient-field homomorphism. No finite action table
or word matrix is constructed. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGFFourNormCertificateSparseWords
open CFSGFFourNormCertificateRootOperators CFSGFFourNormCertificateSparseAction
open CFSGReeFFourFieldEightWordTemplates CFSGReeFFourFieldEightCertificateField
open scoped BigOperators

def rootEnd (K : Type) [Field K] (e : Element →+* K) (x : Letter) :
    Module.End K (Fin 26 → K) :=
  (rootOperator K x.1 x.2.1 (e x.2.2)).mulVecLin

def wordEnd (K : Type) [Field K] (e : Element →+* K) (s : List Letter) :
    Module.End K (Fin 26 → K) := (s.map (rootEnd K e)).prod

theorem wordEnd_cons_apply (K : Type) [Field K] [CharP K 2]
    (e : Element →+* K) (x : Letter) (s : List Letter) (v : Fin 26 → K) :
    wordEnd K e (x :: s) v =
      sparseStep K x.1 x.2.1 (e x.2.2) (wordEnd K e s v) := by
  change (rootEnd K e x * wordEnd K e s) v = _
  rw [Module.End.mul_apply]
  exact (sparseStep_eq_mulVec K x.1 x.2.1 (e x.2.2) _).symm

theorem wordEnd_apply_eq_foldl_reverse (K : Type) [Field K] [CharP K 2]
    (e : Element →+* K) (s : List Letter) (v : Fin 26 → K) :
    wordEnd K e s v =
      s.reverse.foldl (fun u x => sparseStep K x.1 x.2.1 (e x.2.2) u) v := by
  induction s with
  | nil => rfl
  | cons x s ih =>
    rw [wordEnd_cons_apply, ih, List.reverse_cons, List.foldl_append]
    rfl

theorem sparseStep_map (K : Type) [Field K] (e : Element →+* K)
    (neg : Bool) (i : Fin 4) (t : Element) (v : Fin 26 → Element) :
    (fun j => e (sparseStep Element neg i t v j)) =
      sparseStep K neg i (e t) (fun j => e (v j)) := by
  funext j
  simp only [sparseStep, map_add, map_mul, map_pow, map_sum]

theorem wordEnd_map_apply (K : Type) [Field K] [CharP K 2]
    (e : Element →+* K) (s : List Letter) (v : Fin 26 → Element) :
    (fun j => e (wordEnd Element (RingHom.id Element) s v j)) =
      wordEnd K e s (fun j => e (v j)) := by
  induction s with
  | nil => rfl
  | cons x s ih =>
    rw [wordEnd_cons_apply, wordEnd_cons_apply]
    calc
      _ = sparseStep K x.1 x.2.1 (e x.2.2)
          (fun j => e (wordEnd Element (RingHom.id Element) s v j)) :=
        sparseStep_map K e x.1 x.2.1 x.2.2 _
      _ = _ := congrArg (sparseStep K x.1 x.2.1 (e x.2.2)) ih

end SymmetricSubgroupAsymptotics.CFSGFFourNormCertificateSparseWords
