import SymmetricSubgroupAsymptotics.CFSGReeFFourBinaryFirstOrderedBlock
import SymmetricSubgroupAsymptotics.CFSGFFourNormPrimeFieldVectorEvaluation
import Init.Data.Vector.Lemmas
import Mathlib.Data.ZMod.Basic

/-! ONE selected informative commutator entry on the isolated first block.
It is coordinate0 on initial e7, against the actual outer root word x.
Only four exponents a<4 are reduced. Nothing is asserted about this
entry when the other eleven ordered parameters are nonzero. -/
set_option autoImplicit false
set_option Elab.async false
namespace SymmetricSubgroupAsymptotics.CFSGReeFFourBinaryFirstBlockEntry
open CFSGReeFFourBinaryFirstOrderedBlock CFSGReeFFourMiddleDerivedFiveRootWords
open CFSGFFourNormPrimeFieldWords CFSGFFourNormPrimeFieldVectorEvaluation

def initial : Vector (ZMod 2) 26 :=
  Vector.ofFn (fun i : Fin 26 => if i=7 then 1 else 0)

def selectedEntry (a : Fin 4) : ZMod 2 :=
  (materialized (ZMod 2) (firstLetters a++outerLetters) initial)[0]-
    (materialized (ZMod 2) (outerLetters++firstLetters a) initial)[0]

theorem selectedEntry_values (a : Fin 4) :
    selectedEntry a=if a=0 then 0 else 1 := by
  fin_cases a <;> decide +kernel

theorem evaluate_commute_implies_zero (a : Fin 4)
    (h : evaluate (ZMod 2) (firstLetters a++outerLetters) (coordinates (ZMod 2) initial)=
      evaluate (ZMod 2) (outerLetters++firstLetters a) (coordinates (ZMod 2) initial)) :
    a=0 := by
  by_contra ha
  have hv : selectedEntry a=1 := by rw [selectedEntry_values,if_neg ha]
  have hc : coordinates (ZMod 2)
        (materialized (ZMod 2) (firstLetters a++outerLetters) initial) 0=
      coordinates (ZMod 2)
        (materialized (ZMod 2) (outerLetters++firstLetters a) initial) 0 :=
    (congrFun (coordinates_materialized (ZMod 2) (firstLetters a++outerLetters) initial) 0).trans
      ((congrFun h 0).trans
        (congrFun (coordinates_materialized (ZMod 2) (outerLetters++firstLetters a) initial) 0).symm)
  have hz : selectedEntry a=0 := sub_eq_zero.mpr hc
  exact one_ne_zero (hv.symm.trans hz)

end SymmetricSubgroupAsymptotics.CFSGReeFFourBinaryFirstBlockEntry
