import SymmetricSubgroupAsymptotics.GeneratedCarrier16T1086.QuotientRows000
import SymmetricSubgroupAsymptotics.GeneratedCarrier16T1086.QuotientRows001
import SymmetricSubgroupAsymptotics.GeneratedCarrier16T1086.QuotientRows002
import SymmetricSubgroupAsymptotics.GeneratedCarrier16T1086.QuotientRows003
import SymmetricSubgroupAsymptotics.GeneratedCarrier16T1086.QuotientRows004
import SymmetricSubgroupAsymptotics.GeneratedCarrier16T1086.QuotientRows005
import SymmetricSubgroupAsymptotics.GeneratedCarrier16T1086.QuotientRows006
import SymmetricSubgroupAsymptotics.GeneratedCarrier16T1086.QuotientRows007

/-! Selected literal carrier data; all checks use the Lean kernel. -/
set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 100000
noncomputable section
namespace SymmetricSubgroupAsymptotics.BinaryChart16T1086

def quotientCayley : FiniteCayleyCertificate quotientGenerators 256 where
  elements := fun i => quotientElement i
  identity := 0
  identity_eq := by decide +kernel
  next i j := (quotientNextTable i)[j.val]!
  next_eq := by
    intro i
    by_cases h0 : i.val<32
    · exact quotientNextChecked000 i (Nat.zero_le _) h0
    ·
      by_cases h1 : i.val<64
      · exact quotientNextChecked001 i (Nat.le_of_not_gt h0) h1
      ·
        by_cases h2 : i.val<96
        · exact quotientNextChecked002 i (Nat.le_of_not_gt h1) h2
        ·
          by_cases h3 : i.val<128
          · exact quotientNextChecked003 i (Nat.le_of_not_gt h2) h3
          ·
            by_cases h4 : i.val<160
            · exact quotientNextChecked004 i (Nat.le_of_not_gt h3) h4
            ·
              by_cases h5 : i.val<192
              · exact quotientNextChecked005 i (Nat.le_of_not_gt h4) h5
              ·
                by_cases h6 : i.val<224
                · exact quotientNextChecked006 i (Nat.le_of_not_gt h5) h6
                ·
                  exact quotientNextChecked007 i (Nat.le_of_not_gt h6) i.isLt
  words i := quotientWordTable i
  words_eq := by
    intro i
    by_cases h0 : i.val<32
    · exact quotientWordsChecked000 i (Nat.zero_le _) h0
    ·
      by_cases h1 : i.val<64
      · exact quotientWordsChecked001 i (Nat.le_of_not_gt h0) h1
      ·
        by_cases h2 : i.val<96
        · exact quotientWordsChecked002 i (Nat.le_of_not_gt h1) h2
        ·
          by_cases h3 : i.val<128
          · exact quotientWordsChecked003 i (Nat.le_of_not_gt h2) h3
          ·
            by_cases h4 : i.val<160
            · exact quotientWordsChecked004 i (Nat.le_of_not_gt h3) h4
            ·
              by_cases h5 : i.val<192
              · exact quotientWordsChecked005 i (Nat.le_of_not_gt h4) h5
              ·
                by_cases h6 : i.val<224
                · exact quotientWordsChecked006 i (Nat.le_of_not_gt h5) h6
                ·
                  exact quotientWordsChecked007 i (Nat.le_of_not_gt h6) i.isLt

def quotientCertificate := quotientCayley

end SymmetricSubgroupAsymptotics.BinaryChart16T1086
