import SymmetricSubgroupAsymptotics.CFSGMathieuTwelveWittMaskBitmap
import SymmetricSubgroupAsymptotics.CFSGMathieuTwelveYNecessaryWittWhitelistPilot

/-! SAME original codes0..63 and SAME saved bad-hexad witnesses as the checked
old pilot. No new diagnostic or expanded exclusion range. The symbolic decoder
replaces all per-code twelve-point bindings; the necessary bitmap replaces
searching132 Finsets for each image hexad. This is not a full centralizer bound. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGMathieuTwelveYMaskComparisonPilot
open CFSG.Certificates.Mathieu12 M12Certificates.WittDesign
open CFSGMathieuTwelveYCentralizerFiniteEncoding
open CFSGMathieuTwelveYNecessaryWittWhitelistPilot
open CFSGMathieuTwelveWittMaskBitmap

def comparisonBadIndex (i : Fin 64) : Fin 132 :=
  match i.val with
  | 0 => 0
  | 1 => 0
  | 2 => 0
  | 3 => 0
  | 4 => 0
  | 5 => 0
  | 6 => 0
  | 7 => 0
  | 8 => 0
  | 9 => 1
  | 10 => 0
  | 11 => 0
  | 12 => 0
  | 13 => 0
  | 14 => 0
  | 15 => 0
  | 16 => 0
  | 17 => 0
  | 18 => 1
  | 19 => 0
  | 20 => 0
  | 21 => 0
  | 22 => 0
  | 23 => 0
  | 24 => 0
  | 25 => 0
  | 26 => 0
  | 27 => 0
  | 28 => 0
  | 29 => 0
  | 30 => 0
  | 31 => 1
  | 32 => 0
  | 33 => 0
  | 34 => 0
  | 35 => 0
  | 36 => 0
  | 37 => 0
  | 38 => 0
  | 39 => 0
  | 40 => 0
  | 41 => 0
  | 42 => 0
  | 43 => 0
  | 44 => 0
  | 45 => 0
  | 46 => 0
  | 47 => 0
  | 48 => 0
  | 49 => 1
  | 50 => 0
  | 51 => 0
  | 52 => 0
  | 53 => 0
  | 54 => 0
  | 55 => 0
  | 56 => 0
  | 57 => 0
  | 58 => 0
  | 59 => 0
  | 60 => 0
  | 61 => 0
  | 62 => 1
  | _ => 0

private theorem witness_0 : 0 ∈ literalWhitelist ∨
    blockMap (indexedChart 0) (wittBlockAt 0) ∉ wittBlocks := by
  exact Or.inl (by decide +kernel)

private theorem witness_1 : 1 ∈ literalWhitelist ∨
    blockMap (indexedChart 1) (wittBlockAt 0) ∉ wittBlocks := by
  apply Or.inr
  apply rejects_of_raw_mask_false
  decide +kernel

private theorem witness_2 : 2 ∈ literalWhitelist ∨
    blockMap (indexedChart 2) (wittBlockAt 0) ∉ wittBlocks := by
  apply Or.inr
  apply rejects_of_raw_mask_false
  decide +kernel

private theorem witness_3 : 3 ∈ literalWhitelist ∨
    blockMap (indexedChart 3) (wittBlockAt 0) ∉ wittBlocks := by
  apply Or.inr
  apply rejects_of_raw_mask_false
  decide +kernel

private theorem witness_4 : 4 ∈ literalWhitelist ∨
    blockMap (indexedChart 4) (wittBlockAt 0) ∉ wittBlocks := by
  apply Or.inr
  apply rejects_of_raw_mask_false
  decide +kernel

private theorem witness_5 : 5 ∈ literalWhitelist ∨
    blockMap (indexedChart 5) (wittBlockAt 0) ∉ wittBlocks := by
  apply Or.inr
  apply rejects_of_raw_mask_false
  decide +kernel

private theorem witness_6 : 6 ∈ literalWhitelist ∨
    blockMap (indexedChart 6) (wittBlockAt 0) ∉ wittBlocks := by
  apply Or.inr
  apply rejects_of_raw_mask_false
  decide +kernel

private theorem witness_7 : 7 ∈ literalWhitelist ∨
    blockMap (indexedChart 7) (wittBlockAt 0) ∉ wittBlocks := by
  apply Or.inr
  apply rejects_of_raw_mask_false
  decide +kernel

private theorem witness_8 : 8 ∈ literalWhitelist ∨
    blockMap (indexedChart 8) (wittBlockAt 0) ∉ wittBlocks := by
  apply Or.inr
  apply rejects_of_raw_mask_false
  decide +kernel

private theorem witness_9 : 9 ∈ literalWhitelist ∨
    blockMap (indexedChart 9) (wittBlockAt 1) ∉ wittBlocks := by
  apply Or.inr
  apply rejects_of_raw_mask_false
  decide +kernel

private theorem witness_10 : 10 ∈ literalWhitelist ∨
    blockMap (indexedChart 10) (wittBlockAt 0) ∉ wittBlocks := by
  apply Or.inr
  apply rejects_of_raw_mask_false
  decide +kernel

private theorem witness_11 : 11 ∈ literalWhitelist ∨
    blockMap (indexedChart 11) (wittBlockAt 0) ∉ wittBlocks := by
  apply Or.inr
  apply rejects_of_raw_mask_false
  decide +kernel

private theorem witness_12 : 12 ∈ literalWhitelist ∨
    blockMap (indexedChart 12) (wittBlockAt 0) ∉ wittBlocks := by
  apply Or.inr
  apply rejects_of_raw_mask_false
  decide +kernel

private theorem witness_13 : 13 ∈ literalWhitelist ∨
    blockMap (indexedChart 13) (wittBlockAt 0) ∉ wittBlocks := by
  apply Or.inr
  apply rejects_of_raw_mask_false
  decide +kernel

private theorem witness_14 : 14 ∈ literalWhitelist ∨
    blockMap (indexedChart 14) (wittBlockAt 0) ∉ wittBlocks := by
  apply Or.inr
  apply rejects_of_raw_mask_false
  decide +kernel

private theorem witness_15 : 15 ∈ literalWhitelist ∨
    blockMap (indexedChart 15) (wittBlockAt 0) ∉ wittBlocks := by
  apply Or.inr
  apply rejects_of_raw_mask_false
  decide +kernel

private theorem witness_16 : 16 ∈ literalWhitelist ∨
    blockMap (indexedChart 16) (wittBlockAt 0) ∉ wittBlocks := by
  apply Or.inr
  apply rejects_of_raw_mask_false
  decide +kernel

private theorem witness_17 : 17 ∈ literalWhitelist ∨
    blockMap (indexedChart 17) (wittBlockAt 0) ∉ wittBlocks := by
  apply Or.inr
  apply rejects_of_raw_mask_false
  decide +kernel

private theorem witness_18 : 18 ∈ literalWhitelist ∨
    blockMap (indexedChart 18) (wittBlockAt 1) ∉ wittBlocks := by
  apply Or.inr
  apply rejects_of_raw_mask_false
  decide +kernel

private theorem witness_19 : 19 ∈ literalWhitelist ∨
    blockMap (indexedChart 19) (wittBlockAt 0) ∉ wittBlocks := by
  apply Or.inr
  apply rejects_of_raw_mask_false
  decide +kernel

private theorem witness_20 : 20 ∈ literalWhitelist ∨
    blockMap (indexedChart 20) (wittBlockAt 0) ∉ wittBlocks := by
  apply Or.inr
  apply rejects_of_raw_mask_false
  decide +kernel

private theorem witness_21 : 21 ∈ literalWhitelist ∨
    blockMap (indexedChart 21) (wittBlockAt 0) ∉ wittBlocks := by
  apply Or.inr
  apply rejects_of_raw_mask_false
  decide +kernel

private theorem witness_22 : 22 ∈ literalWhitelist ∨
    blockMap (indexedChart 22) (wittBlockAt 0) ∉ wittBlocks := by
  apply Or.inr
  apply rejects_of_raw_mask_false
  decide +kernel

private theorem witness_23 : 23 ∈ literalWhitelist ∨
    blockMap (indexedChart 23) (wittBlockAt 0) ∉ wittBlocks := by
  apply Or.inr
  apply rejects_of_raw_mask_false
  decide +kernel

private theorem witness_24 : 24 ∈ literalWhitelist ∨
    blockMap (indexedChart 24) (wittBlockAt 0) ∉ wittBlocks := by
  apply Or.inr
  apply rejects_of_raw_mask_false
  decide +kernel

private theorem witness_25 : 25 ∈ literalWhitelist ∨
    blockMap (indexedChart 25) (wittBlockAt 0) ∉ wittBlocks := by
  apply Or.inr
  apply rejects_of_raw_mask_false
  decide +kernel

private theorem witness_26 : 26 ∈ literalWhitelist ∨
    blockMap (indexedChart 26) (wittBlockAt 0) ∉ wittBlocks := by
  apply Or.inr
  apply rejects_of_raw_mask_false
  decide +kernel

private theorem witness_27 : 27 ∈ literalWhitelist ∨
    blockMap (indexedChart 27) (wittBlockAt 0) ∉ wittBlocks := by
  apply Or.inr
  apply rejects_of_raw_mask_false
  decide +kernel

private theorem witness_28 : 28 ∈ literalWhitelist ∨
    blockMap (indexedChart 28) (wittBlockAt 0) ∉ wittBlocks := by
  apply Or.inr
  apply rejects_of_raw_mask_false
  decide +kernel

private theorem witness_29 : 29 ∈ literalWhitelist ∨
    blockMap (indexedChart 29) (wittBlockAt 0) ∉ wittBlocks := by
  apply Or.inr
  apply rejects_of_raw_mask_false
  decide +kernel

private theorem witness_30 : 30 ∈ literalWhitelist ∨
    blockMap (indexedChart 30) (wittBlockAt 0) ∉ wittBlocks := by
  apply Or.inr
  apply rejects_of_raw_mask_false
  decide +kernel

private theorem witness_31 : 31 ∈ literalWhitelist ∨
    blockMap (indexedChart 31) (wittBlockAt 1) ∉ wittBlocks := by
  apply Or.inr
  apply rejects_of_raw_mask_false
  decide +kernel

private theorem witness_32 : 32 ∈ literalWhitelist ∨
    blockMap (indexedChart 32) (wittBlockAt 0) ∉ wittBlocks := by
  apply Or.inr
  apply rejects_of_raw_mask_false
  decide +kernel

private theorem witness_33 : 33 ∈ literalWhitelist ∨
    blockMap (indexedChart 33) (wittBlockAt 0) ∉ wittBlocks := by
  apply Or.inr
  apply rejects_of_raw_mask_false
  decide +kernel

private theorem witness_34 : 34 ∈ literalWhitelist ∨
    blockMap (indexedChart 34) (wittBlockAt 0) ∉ wittBlocks := by
  apply Or.inr
  apply rejects_of_raw_mask_false
  decide +kernel

private theorem witness_35 : 35 ∈ literalWhitelist ∨
    blockMap (indexedChart 35) (wittBlockAt 0) ∉ wittBlocks := by
  apply Or.inr
  apply rejects_of_raw_mask_false
  decide +kernel

private theorem witness_36 : 36 ∈ literalWhitelist ∨
    blockMap (indexedChart 36) (wittBlockAt 0) ∉ wittBlocks := by
  apply Or.inr
  apply rejects_of_raw_mask_false
  decide +kernel

private theorem witness_37 : 37 ∈ literalWhitelist ∨
    blockMap (indexedChart 37) (wittBlockAt 0) ∉ wittBlocks := by
  apply Or.inr
  apply rejects_of_raw_mask_false
  decide +kernel

private theorem witness_38 : 38 ∈ literalWhitelist ∨
    blockMap (indexedChart 38) (wittBlockAt 0) ∉ wittBlocks := by
  apply Or.inr
  apply rejects_of_raw_mask_false
  decide +kernel

private theorem witness_39 : 39 ∈ literalWhitelist ∨
    blockMap (indexedChart 39) (wittBlockAt 0) ∉ wittBlocks := by
  apply Or.inr
  apply rejects_of_raw_mask_false
  decide +kernel

private theorem witness_40 : 40 ∈ literalWhitelist ∨
    blockMap (indexedChart 40) (wittBlockAt 0) ∉ wittBlocks := by
  exact Or.inl (by decide +kernel)

private theorem witness_41 : 41 ∈ literalWhitelist ∨
    blockMap (indexedChart 41) (wittBlockAt 0) ∉ wittBlocks := by
  apply Or.inr
  apply rejects_of_raw_mask_false
  decide +kernel

private theorem witness_42 : 42 ∈ literalWhitelist ∨
    blockMap (indexedChart 42) (wittBlockAt 0) ∉ wittBlocks := by
  apply Or.inr
  apply rejects_of_raw_mask_false
  decide +kernel

private theorem witness_43 : 43 ∈ literalWhitelist ∨
    blockMap (indexedChart 43) (wittBlockAt 0) ∉ wittBlocks := by
  apply Or.inr
  apply rejects_of_raw_mask_false
  decide +kernel

private theorem witness_44 : 44 ∈ literalWhitelist ∨
    blockMap (indexedChart 44) (wittBlockAt 0) ∉ wittBlocks := by
  apply Or.inr
  apply rejects_of_raw_mask_false
  decide +kernel

private theorem witness_45 : 45 ∈ literalWhitelist ∨
    blockMap (indexedChart 45) (wittBlockAt 0) ∉ wittBlocks := by
  apply Or.inr
  apply rejects_of_raw_mask_false
  decide +kernel

private theorem witness_46 : 46 ∈ literalWhitelist ∨
    blockMap (indexedChart 46) (wittBlockAt 0) ∉ wittBlocks := by
  apply Or.inr
  apply rejects_of_raw_mask_false
  decide +kernel

private theorem witness_47 : 47 ∈ literalWhitelist ∨
    blockMap (indexedChart 47) (wittBlockAt 0) ∉ wittBlocks := by
  apply Or.inr
  apply rejects_of_raw_mask_false
  decide +kernel

private theorem witness_48 : 48 ∈ literalWhitelist ∨
    blockMap (indexedChart 48) (wittBlockAt 0) ∉ wittBlocks := by
  apply Or.inr
  apply rejects_of_raw_mask_false
  decide +kernel

private theorem witness_49 : 49 ∈ literalWhitelist ∨
    blockMap (indexedChart 49) (wittBlockAt 1) ∉ wittBlocks := by
  apply Or.inr
  apply rejects_of_raw_mask_false
  decide +kernel

private theorem witness_50 : 50 ∈ literalWhitelist ∨
    blockMap (indexedChart 50) (wittBlockAt 0) ∉ wittBlocks := by
  apply Or.inr
  apply rejects_of_raw_mask_false
  decide +kernel

private theorem witness_51 : 51 ∈ literalWhitelist ∨
    blockMap (indexedChart 51) (wittBlockAt 0) ∉ wittBlocks := by
  apply Or.inr
  apply rejects_of_raw_mask_false
  decide +kernel

private theorem witness_52 : 52 ∈ literalWhitelist ∨
    blockMap (indexedChart 52) (wittBlockAt 0) ∉ wittBlocks := by
  apply Or.inr
  apply rejects_of_raw_mask_false
  decide +kernel

private theorem witness_53 : 53 ∈ literalWhitelist ∨
    blockMap (indexedChart 53) (wittBlockAt 0) ∉ wittBlocks := by
  apply Or.inr
  apply rejects_of_raw_mask_false
  decide +kernel

private theorem witness_54 : 54 ∈ literalWhitelist ∨
    blockMap (indexedChart 54) (wittBlockAt 0) ∉ wittBlocks := by
  apply Or.inr
  apply rejects_of_raw_mask_false
  decide +kernel

private theorem witness_55 : 55 ∈ literalWhitelist ∨
    blockMap (indexedChart 55) (wittBlockAt 0) ∉ wittBlocks := by
  apply Or.inr
  apply rejects_of_raw_mask_false
  decide +kernel

private theorem witness_56 : 56 ∈ literalWhitelist ∨
    blockMap (indexedChart 56) (wittBlockAt 0) ∉ wittBlocks := by
  apply Or.inr
  apply rejects_of_raw_mask_false
  decide +kernel

private theorem witness_57 : 57 ∈ literalWhitelist ∨
    blockMap (indexedChart 57) (wittBlockAt 0) ∉ wittBlocks := by
  apply Or.inr
  apply rejects_of_raw_mask_false
  decide +kernel

private theorem witness_58 : 58 ∈ literalWhitelist ∨
    blockMap (indexedChart 58) (wittBlockAt 0) ∉ wittBlocks := by
  apply Or.inr
  apply rejects_of_raw_mask_false
  decide +kernel

private theorem witness_59 : 59 ∈ literalWhitelist ∨
    blockMap (indexedChart 59) (wittBlockAt 0) ∉ wittBlocks := by
  apply Or.inr
  apply rejects_of_raw_mask_false
  decide +kernel

private theorem witness_60 : 60 ∈ literalWhitelist ∨
    blockMap (indexedChart 60) (wittBlockAt 0) ∉ wittBlocks := by
  apply Or.inr
  apply rejects_of_raw_mask_false
  decide +kernel

private theorem witness_61 : 61 ∈ literalWhitelist ∨
    blockMap (indexedChart 61) (wittBlockAt 0) ∉ wittBlocks := by
  apply Or.inr
  apply rejects_of_raw_mask_false
  decide +kernel

private theorem witness_62 : 62 ∈ literalWhitelist ∨
    blockMap (indexedChart 62) (wittBlockAt 1) ∉ wittBlocks := by
  apply Or.inr
  apply rejects_of_raw_mask_false
  decide +kernel

private theorem witness_63 : 63 ∈ literalWhitelist ∨
    blockMap (indexedChart 63) (wittBlockAt 0) ∉ wittBlocks := by
  apply Or.inr
  apply rejects_of_raw_mask_false
  decide +kernel

theorem comparison_witnesses (i : Fin 64) : pilotIndex i ∈ literalWhitelist ∨
    blockMap (indexedChart (pilotIndex i)) (wittBlockAt (comparisonBadIndex i)) ∉ wittBlocks := by
  fin_cases i
  · exact witness_0
  · exact witness_1
  · exact witness_2
  · exact witness_3
  · exact witness_4
  · exact witness_5
  · exact witness_6
  · exact witness_7
  · exact witness_8
  · exact witness_9
  · exact witness_10
  · exact witness_11
  · exact witness_12
  · exact witness_13
  · exact witness_14
  · exact witness_15
  · exact witness_16
  · exact witness_17
  · exact witness_18
  · exact witness_19
  · exact witness_20
  · exact witness_21
  · exact witness_22
  · exact witness_23
  · exact witness_24
  · exact witness_25
  · exact witness_26
  · exact witness_27
  · exact witness_28
  · exact witness_29
  · exact witness_30
  · exact witness_31
  · exact witness_32
  · exact witness_33
  · exact witness_34
  · exact witness_35
  · exact witness_36
  · exact witness_37
  · exact witness_38
  · exact witness_39
  · exact witness_40
  · exact witness_41
  · exact witness_42
  · exact witness_43
  · exact witness_44
  · exact witness_45
  · exact witness_46
  · exact witness_47
  · exact witness_48
  · exact witness_49
  · exact witness_50
  · exact witness_51
  · exact witness_52
  · exact witness_53
  · exact witness_54
  · exact witness_55
  · exact witness_56
  · exact witness_57
  · exact witness_58
  · exact witness_59
  · exact witness_60
  · exact witness_61
  · exact witness_62
  · exact witness_63

end SymmetricSubgroupAsymptotics.CFSGMathieuTwelveYMaskComparisonPilot
