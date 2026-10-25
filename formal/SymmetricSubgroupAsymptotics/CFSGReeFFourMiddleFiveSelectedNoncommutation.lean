import SymmetricSubgroupAsymptotics.CFSGFFourNormPrimeFieldVectorEvaluation
import SymmetricSubgroupAsymptotics.CFSGReeFFourMiddleDerivedFiveRootWords
import Init.Data.Vector.Lemmas
import Mathlib.Data.ZMod.Basic

/-! One literal selected-vector inequality over the prime field. The two
48-root words are the order-five word and positive commutator in opposite
orders. No word search, full matrix, or group-order input is involved. -/
set_option autoImplicit false
set_option Elab.async false
namespace SymmetricSubgroupAsymptotics.CFSGReeFFourMiddleFiveSelectedNoncommutation
open CFSGFFourNormPrimeFieldWords CFSGFFourNormPrimeFieldVectorEvaluation
open CFSGReeFFourMiddleDerivedFiveRootWords

def initial : Vector (ZMod 2) 26 :=
  Vector.ofFn (fun i : Fin 26 => if i = 0 then 1 else 0)

theorem selected_left_fourteen :
    (materialized (ZMod 2) (fiveLetters ++ positiveCommutatorLetters) initial)[14] = 1 := by
  decide +kernel

theorem selected_right_fourteen :
    (materialized (ZMod 2) (positiveCommutatorLetters ++ fiveLetters) initial)[14] = 0 := by
  decide +kernel

theorem selected_noncommutation :
    materialized (ZMod 2) (fiveLetters ++ positiveCommutatorLetters) initial ≠
      materialized (ZMod 2) (positiveCommutatorLetters ++ fiveLetters) initial := by
  intro h
  have hc : (1 : ZMod 2) = 0 := selected_left_fourteen.symm.trans
    ((congrArg (fun v : Vector (ZMod 2) 26 => v[14]) h).trans selected_right_fourteen)
  exact one_ne_zero hc

theorem selected_evaluate_ne :
    evaluate (ZMod 2) (fiveLetters ++ positiveCommutatorLetters)
        (coordinates (ZMod 2) initial) ≠
      evaluate (ZMod 2) (positiveCommutatorLetters ++ fiveLetters)
        (coordinates (ZMod 2) initial) := by
  intro h
  apply selected_noncommutation
  apply Vector.ext
  intro i hi
  have hh : coordinates (ZMod 2)
      (materialized (ZMod 2) (fiveLetters ++ positiveCommutatorLetters) initial) =
      coordinates (ZMod 2)
        (materialized (ZMod 2) (positiveCommutatorLetters ++ fiveLetters) initial) := by
    simpa only [coordinates_materialized] using h
  exact congrFun hh ⟨i,hi⟩

theorem selected_evaluate_map_ne (K : Type) [Field K] [CharP K 2] :
    let e : ZMod 2 →+* K := ZMod.castHom (dvd_refl 2) K
    evaluate K (fiveLetters ++ positiveCommutatorLetters)
        (fun j => e (coordinates (ZMod 2) initial j)) ≠
      evaluate K (positiveCommutatorLetters ++ fiveLetters)
        (fun j => e (coordinates (ZMod 2) initial j)) := by
  dsimp only
  let e : ZMod 2 →+* K := ZMod.castHom (dvd_refl 2) K
  intro h
  apply selected_evaluate_ne
  funext j
  apply e.injective
  calc
    _ = evaluate K (fiveLetters ++ positiveCommutatorLetters)
        (fun j => e (coordinates (ZMod 2) initial j)) j :=
      congrFun (evaluate_map (ZMod 2) K e _ _) j
    _ = evaluate K (positiveCommutatorLetters ++ fiveLetters)
        (fun j => e (coordinates (ZMod 2) initial j)) j := congrFun h j
    _ = _ := (congrFun (evaluate_map (ZMod 2) K e _ _) j).symm

end SymmetricSubgroupAsymptotics.CFSGReeFFourMiddleFiveSelectedNoncommutation
