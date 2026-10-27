import SymmetricSubgroupAsymptotics.MatrixNaturalRowPowerReflection
import SymmetricSubgroupAsymptotics.External.CFSG.Models.MatrixGroups.Ru
set_option autoImplicit false
set_option Elab.async false
namespace SymmetricSubgroupAsymptotics.CFSGRuFirstPackedSourceColumns
open MatrixNaturalRowDotReflection CFSG.Models.MatrixGroups.Ru

def columnCode (z : ℕ) : ℕ :=
  match z with
  | 0 => 87581437
  | 1 => 4845241
  | 2 => 13867548
  | 3 => 152638358
  | 4 => 185492002
  | 5 => 91322832
  | 6 => 176329496
  | 7 => 164046377
  | 8 => 191425457
  | 9 => 133837578
  | 10 => 187165980
  | 11 => 72687628
  | 12 => 195159101
  | 13 => 246101920
  | 14 => 179428578
  | 15 => 233756646
  | 16 => 21295078
  | 17 => 218231520
  | 18 => 192746356
  | 19 => 56351310
  | 20 => 177424599
  | 21 => 200118068
  | 22 => 150649764
  | 23 => 151528708
  | 24 => 255605147
  | 25 => 236127668
  | 26 => 254917067
  | 27 => 47204548
  | _ => 0

theorem source_column_binding : ∀ (z j : Fin 28),
    rawDigit rows1 j.val z.val = packedDigit 1 (columnCode z.val) j.val := by
  decide +kernel

end SymmetricSubgroupAsymptotics.CFSGRuFirstPackedSourceColumns
