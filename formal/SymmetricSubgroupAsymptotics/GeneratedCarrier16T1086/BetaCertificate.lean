import SymmetricSubgroupAsymptotics.GeneratedCarrier16T1086.BetaRows000
import SymmetricSubgroupAsymptotics.GeneratedCarrier16T1086.BetaRows001
import SymmetricSubgroupAsymptotics.GeneratedCarrier16T1086.BetaRows002
import SymmetricSubgroupAsymptotics.GeneratedCarrier16T1086.BetaRows003
import SymmetricSubgroupAsymptotics.GeneratedCarrier16T1086.BetaRows004
import SymmetricSubgroupAsymptotics.GeneratedCarrier16T1086.BetaRows005
import SymmetricSubgroupAsymptotics.GeneratedCarrier16T1086.BetaRows006
import SymmetricSubgroupAsymptotics.GeneratedCarrier16T1086.BetaRows007

/-! Selected literal carrier data; all checks use the Lean kernel. -/
set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 100000
noncomputable section
namespace SymmetricSubgroupAsymptotics.BinaryChart16T1086

def betaCayley : FiniteCayleyCertificate (fun j => (betaGenerators j, betaImages j)) 256 where
  elements := fun i => (betaSource i, betaTarget i)
  identity := 0
  identity_eq := by decide +kernel
  next i j := (betaNextTable i)[j.val]!
  next_eq := by
    intro i
    by_cases h0 : i.val<32
    · exact betaNextChecked000 i (Nat.zero_le _) h0
    ·
      by_cases h1 : i.val<64
      · exact betaNextChecked001 i (Nat.le_of_not_gt h0) h1
      ·
        by_cases h2 : i.val<96
        · exact betaNextChecked002 i (Nat.le_of_not_gt h1) h2
        ·
          by_cases h3 : i.val<128
          · exact betaNextChecked003 i (Nat.le_of_not_gt h2) h3
          ·
            by_cases h4 : i.val<160
            · exact betaNextChecked004 i (Nat.le_of_not_gt h3) h4
            ·
              by_cases h5 : i.val<192
              · exact betaNextChecked005 i (Nat.le_of_not_gt h4) h5
              ·
                by_cases h6 : i.val<224
                · exact betaNextChecked006 i (Nat.le_of_not_gt h5) h6
                ·
                  exact betaNextChecked007 i (Nat.le_of_not_gt h6) i.isLt
  words i := betaWordTable i
  words_eq := by
    intro i
    by_cases h0 : i.val<32
    · exact betaWordsChecked000 i (Nat.zero_le _) h0
    ·
      by_cases h1 : i.val<64
      · exact betaWordsChecked001 i (Nat.le_of_not_gt h0) h1
      ·
        by_cases h2 : i.val<96
        · exact betaWordsChecked002 i (Nat.le_of_not_gt h1) h2
        ·
          by_cases h3 : i.val<128
          · exact betaWordsChecked003 i (Nat.le_of_not_gt h2) h3
          ·
            by_cases h4 : i.val<160
            · exact betaWordsChecked004 i (Nat.le_of_not_gt h3) h4
            ·
              by_cases h5 : i.val<192
              · exact betaWordsChecked005 i (Nat.le_of_not_gt h4) h5
              ·
                by_cases h6 : i.val<224
                · exact betaWordsChecked006 i (Nat.le_of_not_gt h5) h6
                ·
                  exact betaWordsChecked007 i (Nat.le_of_not_gt h6) i.isLt

def betaCertificate : FiniteHomCertificate betaGenerators betaImages 256 where
  cayley := betaCayley
  first_kernel := by
    intro i
    by_cases h0 : i.val<32
    · exact betaFirstKernelChecked000 i (Nat.zero_le _) h0
    ·
      by_cases h1 : i.val<64
      · exact betaFirstKernelChecked001 i (Nat.le_of_not_gt h0) h1
      ·
        by_cases h2 : i.val<96
        · exact betaFirstKernelChecked002 i (Nat.le_of_not_gt h1) h2
        ·
          by_cases h3 : i.val<128
          · exact betaFirstKernelChecked003 i (Nat.le_of_not_gt h2) h3
          ·
            by_cases h4 : i.val<160
            · exact betaFirstKernelChecked004 i (Nat.le_of_not_gt h3) h4
            ·
              by_cases h5 : i.val<192
              · exact betaFirstKernelChecked005 i (Nat.le_of_not_gt h4) h5
              ·
                by_cases h6 : i.val<224
                · exact betaFirstKernelChecked006 i (Nat.le_of_not_gt h5) h6
                ·
                  exact betaFirstKernelChecked007 i (Nat.le_of_not_gt h6) i.isLt

end SymmetricSubgroupAsymptotics.BinaryChart16T1086
