import SymmetricSubgroupAsymptotics.BinaryLocalAlternatingFourPolynomial

/-! Two binary plane coordinates give two copies of the checked natural
quartet polynomial. This uses the same eight-coordinate interface as the
cubic-twist certificate. -/
set_option autoImplicit false
noncomputable section
open scoped BigOperators
namespace SymmetricSubgroupAsymptotics.BinaryUntwistedQuartetPolynomial
abbrev Bit := ZMod 2
abbrev Vector := Fin 8 → Bit

def matrix : Matrix (Fin 8) (Fin 8) Bit := fun i j =>
  if i.val%2=j.val%2 then
    BinaryLocalAlternatingFourPolynomial.matrix Bit
      ⟨i.val/2,by omega⟩ ⟨j.val/2,by omega⟩ else 0

def operator : Module.End Bit Vector := matrix.mulVecLin

def vectors (s : Fin 2) (m : Fin 4) (i : Fin 8) : Bit :=
  if i.val%2=s.val then
    BinaryLocalAlternatingFourPolynomial.vectors Bit 0 m ⟨i.val/2,by omega⟩ else 0

def selected (j : Fin 8) : Fin 2 × Fin 4 :=
  (⟨j.val/4,by omega⟩,⟨j.val%4,by omega⟩)

def coefficient (i j : Fin 8) : Bit :=
  if i.val%2=(selected j).1.val then
    BinaryLocalAlternatingFourPolynomial.coefficient Bit
      ⟨i.val/2,by omega⟩ (selected j).2 else 0

def witness : LiteralPolynomialSpanWitness operator 2 3 where
  vectors := vectors
  step j m := by
    funext x
    revert j m x
    decide +kernel
  selected := selected
  coefficient := coefficient
  point_eq := by decide +kernel

end SymmetricSubgroupAsymptotics.BinaryUntwistedQuartetPolynomial
