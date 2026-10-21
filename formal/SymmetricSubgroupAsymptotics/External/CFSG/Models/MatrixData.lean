import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
import Mathlib.Data.ZMod.Basic

namespace CFSG.Models.MatrixData

/-- ASCII decimal digits, one string per row. The data audit checks every
length and character; the total decoder itself needs no existence assumption. -/
def matrix (p n : ℕ) (rows : Array String) : Matrix (Fin n) (Fin n) (ZMod p) :=
  fun i j => ((rows[i.val]!.toUTF8[j.val]!).toNat - 48 : ℕ)

/-- All units with either of the two literal coordinate arrays. Invertibility
of the supplied arrays is independently checked by modular row reduction in
`scripts/import_atlas.py`; that check is not a Lean theorem. -/
def generators (p n : ℕ) (a b : Array String) :
    Set (Matrix.GeneralLinearGroup (Fin n) (ZMod p)) :=
  {g | (g : Matrix (Fin n) (Fin n) (ZMod p)) = matrix p n a ∨
       (g : Matrix (Fin n) (Fin n) (ZMod p)) = matrix p n b}

abbrev Model (p n : ℕ) (a b : Array String) :=
  ↥(Subgroup.closure (generators p n a b))

end CFSG.Models.MatrixData
