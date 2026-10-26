import SymmetricSubgroupAsymptotics.BinaryPackedMatrix
import SymmetricSubgroupAsymptotics.CFSGReeFFourBinaryOrderedMatrixData
import Mathlib.Tactic.FinCases

/-! Twelve ALREADY-CHECKED literal row-support tables repacked as Nat masks.
No new matrix products or tuple classification are performed by the producer.
Every decoded entry is independently checked by the Lean kernel. -/
set_option autoImplicit false
set_option Elab.async false
namespace SymmetricSubgroupAsymptotics.CFSGReeFFourPackedOrderedBitMatrices
open BinaryPackedMatrix CFSGReeFFourBinaryOrderedMatrixData

def packedBits : Fin 12 → Rows 26 :=
  ![![1,12290,4,8,24,48,120,128,384,768,1920,2048,4096,12288,16384,40961,81920,176128,327680,868352,1048576,2097152,6291456,12582912,31457280,33554432],
    ![1,4098,4,8,16,40,88,128,256,640,1408,2048,4096,8192,16384,36864,65536,143361,278528,606208,1048576,2097152,4194304,10485760,23068672,33554432],
    ![129,2,4,8,16,32,68,128,256,520,1040,2056,4096,8192,16384,33024,69632,133640,270336,524418,1052672,2097152,4194304,8404992,17895424,35651584],
    ![265,266,4,8,16,36,64,128,264,512,1056,2064,4096,8320,20480,34816,65536,132132,262403,559120,1056768,2097152,4210688,9445504,17039624,37769216],
    ![9,10,4,8,16,32,64,128,256,512,1028,2048,4096,8192,16384,32784,65536,131108,262152,526352,1048704,2097152,4198400,8396928,16777483,33574912],
    ![17,2,4,8,16,32,64,128,256,516,1024,2048,4096,8200,16384,32772,65544,131136,264192,524320,1048832,2101248,4194432,8388626,16810500,33628168],
    ![1,2054,4,8,16,32,64,136,272,544,1088,2052,4096,8192,16512,32768,65792,131072,262656,525312,1050625,2113672,4260112,8651296,17302592,34605060],
    ![1,6,4,8,16,32,64,128,256,512,1024,2048,4096,8192,16392,32768,65552,131072,262176,524352,1048580,2097288,4194576,8389152,16778304,33556485],
    ![33,2,4,8,16,32,64,128,260,512,1024,2048,4104,8196,16400,32832,67584,131072,262208,524288,1049088,2105604,4194338,8389632,16908288,33849408],
    ![577,578,4,8,20,32,64,144,256,576,1024,2080,4244,10240,26656,33792,66051,131072,262144,655360,1081344,2163264,5276672,8912896,16777216,42598400],
    ![65,66,4,8,16,32,64,132,256,512,1024,2048,4116,8224,18464,32768,65600,131072,262144,524288,1049600,2097731,4228096,8519680,16777216,34209792],
    ![1025,2,4,12,16,32,64,160,320,512,1024,2112,6464,8704,17410,32768,98304,131072,393216,524288,1179648,3538944,4718592,8388608,16777216,50331648]]

private theorem entry0 : ∀i j : Fin 26,
    bit (packedBits 0 i) j.val=bitMatrix 0 i j := by
  decide +kernel

private theorem entry1 : ∀i j : Fin 26,
    bit (packedBits 1 i) j.val=bitMatrix 1 i j := by
  decide +kernel

private theorem entry2 : ∀i j : Fin 26,
    bit (packedBits 2 i) j.val=bitMatrix 2 i j := by
  decide +kernel

private theorem entry3 : ∀i j : Fin 26,
    bit (packedBits 3 i) j.val=bitMatrix 3 i j := by
  decide +kernel

private theorem entry4 : ∀i j : Fin 26,
    bit (packedBits 4 i) j.val=bitMatrix 4 i j := by
  decide +kernel

private theorem entry5 : ∀i j : Fin 26,
    bit (packedBits 5 i) j.val=bitMatrix 5 i j := by
  decide +kernel

private theorem entry6 : ∀i j : Fin 26,
    bit (packedBits 6 i) j.val=bitMatrix 6 i j := by
  decide +kernel

private theorem entry7 : ∀i j : Fin 26,
    bit (packedBits 7 i) j.val=bitMatrix 7 i j := by
  decide +kernel

private theorem entry8 : ∀i j : Fin 26,
    bit (packedBits 8 i) j.val=bitMatrix 8 i j := by
  decide +kernel

private theorem entry9 : ∀i j : Fin 26,
    bit (packedBits 9 i) j.val=bitMatrix 9 i j := by
  decide +kernel

private theorem entry10 : ∀i j : Fin 26,
    bit (packedBits 10 i) j.val=bitMatrix 10 i j := by
  decide +kernel

private theorem entry11 : ∀i j : Fin 26,
    bit (packedBits 11 i) j.val=bitMatrix 11 i j := by
  decide +kernel

theorem packedBits_entry (k : Fin 12) (i j : Fin 26) :
    bit (packedBits k i) j.val=bitMatrix k i j := by
  fin_cases k
  · exact entry0 i j
  · exact entry1 i j
  · exact entry2 i j
  · exact entry3 i j
  · exact entry4 i j
  · exact entry5 i j
  · exact entry6 i j
  · exact entry7 i j
  · exact entry8 i j
  · exact entry9 i j
  · exact entry10 i j
  · exact entry11 i j

theorem decode_packedBits (k : Fin 12) : decode (packedBits k)=bitMatrix k := by
  ext i j
  exact packedBits_entry k i j

end SymmetricSubgroupAsymptotics.CFSGReeFFourPackedOrderedBitMatrices
