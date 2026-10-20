import SymmetricSubgroupAsymptotics.GeneratedCarrier16T1086.BetaCertificate
import SymmetricSubgroupAsymptotics.GeneratedCarrier16T1086.QuotientCertificate
import SymmetricSubgroupAsymptotics.GeneratedCarrier16T1086.CoverKernelCertificate
import SymmetricSubgroupAsymptotics.GeneratedCarrier16T1086.BetaRangeForwardCheck000
import SymmetricSubgroupAsymptotics.GeneratedCarrier16T1086.BetaRangeForwardCheck001
import SymmetricSubgroupAsymptotics.GeneratedCarrier16T1086.BetaRangeForwardCheck002
import SymmetricSubgroupAsymptotics.GeneratedCarrier16T1086.BetaRangeForwardCheck003
import SymmetricSubgroupAsymptotics.GeneratedCarrier16T1086.BetaRangeForwardCheck004
import SymmetricSubgroupAsymptotics.GeneratedCarrier16T1086.BetaRangeForwardCheck005
import SymmetricSubgroupAsymptotics.GeneratedCarrier16T1086.BetaRangeForwardCheck006
import SymmetricSubgroupAsymptotics.GeneratedCarrier16T1086.BetaRangeForwardCheck007
import SymmetricSubgroupAsymptotics.GeneratedCarrier16T1086.BetaRangeBackwardCheck000
import SymmetricSubgroupAsymptotics.GeneratedCarrier16T1086.BetaRangeBackwardCheck001
import SymmetricSubgroupAsymptotics.GeneratedCarrier16T1086.BetaRangeBackwardCheck002
import SymmetricSubgroupAsymptotics.GeneratedCarrier16T1086.BetaRangeBackwardCheck003
import SymmetricSubgroupAsymptotics.GeneratedCarrier16T1086.BetaRangeBackwardCheck004
import SymmetricSubgroupAsymptotics.GeneratedCarrier16T1086.BetaRangeBackwardCheck005
import SymmetricSubgroupAsymptotics.GeneratedCarrier16T1086.BetaRangeBackwardCheck006
import SymmetricSubgroupAsymptotics.GeneratedCarrier16T1086.BetaRangeBackwardCheck007
import SymmetricSubgroupAsymptotics.GeneratedCarrier16T1086.BetaKernelForwardCheck000
import SymmetricSubgroupAsymptotics.GeneratedCarrier16T1086.BetaKernelForwardCheck001
import SymmetricSubgroupAsymptotics.GeneratedCarrier16T1086.BetaKernelForwardCheck002
import SymmetricSubgroupAsymptotics.GeneratedCarrier16T1086.BetaKernelForwardCheck003
import SymmetricSubgroupAsymptotics.GeneratedCarrier16T1086.BetaKernelForwardCheck004
import SymmetricSubgroupAsymptotics.GeneratedCarrier16T1086.BetaKernelForwardCheck005
import SymmetricSubgroupAsymptotics.GeneratedCarrier16T1086.BetaKernelForwardCheck006
import SymmetricSubgroupAsymptotics.GeneratedCarrier16T1086.BetaKernelForwardCheck007
import SymmetricSubgroupAsymptotics.GeneratedCarrier16T1086.BetaKernelBackwardCheck000

/-! Selected literal carrier data; all checks use the Lean kernel. -/
set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 100000
noncomputable section
namespace SymmetricSubgroupAsymptotics.BinaryChart16T1086

theorem beta_range : betaCertificate.hom.range =
    Subgroup.closure (Set.range quotientGenerators) :=
  betaCertificate.hom_range_eq_of_rows quotientCertificate
    betaRangeForward betaRangeBackward
    (by
      intro i
      by_cases h0 : i.val<32
      · exact betaRangeForwardChecked000 i (Nat.zero_le _) h0
      ·
        by_cases h1 : i.val<64
        · exact betaRangeForwardChecked001 i (Nat.le_of_not_gt h0) h1
        ·
          by_cases h2 : i.val<96
          · exact betaRangeForwardChecked002 i (Nat.le_of_not_gt h1) h2
          ·
            by_cases h3 : i.val<128
            · exact betaRangeForwardChecked003 i (Nat.le_of_not_gt h2) h3
            ·
              by_cases h4 : i.val<160
              · exact betaRangeForwardChecked004 i (Nat.le_of_not_gt h3) h4
              ·
                by_cases h5 : i.val<192
                · exact betaRangeForwardChecked005 i (Nat.le_of_not_gt h4) h5
                ·
                  by_cases h6 : i.val<224
                  · exact betaRangeForwardChecked006 i (Nat.le_of_not_gt h5) h6
                  ·
                    exact betaRangeForwardChecked007 i (Nat.le_of_not_gt h6) i.isLt)
    (by
      intro i
      by_cases h0 : i.val<32
      · exact betaRangeBackwardChecked000 i (Nat.zero_le _) h0
      ·
        by_cases h1 : i.val<64
        · exact betaRangeBackwardChecked001 i (Nat.le_of_not_gt h0) h1
        ·
          by_cases h2 : i.val<96
          · exact betaRangeBackwardChecked002 i (Nat.le_of_not_gt h1) h2
          ·
            by_cases h3 : i.val<128
            · exact betaRangeBackwardChecked003 i (Nat.le_of_not_gt h2) h3
            ·
              by_cases h4 : i.val<160
              · exact betaRangeBackwardChecked004 i (Nat.le_of_not_gt h3) h4
              ·
                by_cases h5 : i.val<192
                · exact betaRangeBackwardChecked005 i (Nat.le_of_not_gt h4) h5
                ·
                  by_cases h6 : i.val<224
                  · exact betaRangeBackwardChecked006 i (Nat.le_of_not_gt h5) h6
                  ·
                    exact betaRangeBackwardChecked007 i (Nat.le_of_not_gt h6) i.isLt)

theorem beta_kernel : betaCertificate.hom.ker.map
    (Subgroup.closure (Set.range betaGenerators)).subtype =
      Subgroup.closure (Set.range coverKernelGenerators) :=
  betaCertificate.kernel_image_eq_of_rows coverKernelCertificate
    betaKernelForward betaKernelBackward
    (by
      intro i
      by_cases h0 : i.val<32
      · exact betaKernelForwardChecked000 i (Nat.zero_le _) h0
      ·
        by_cases h1 : i.val<64
        · exact betaKernelForwardChecked001 i (Nat.le_of_not_gt h0) h1
        ·
          by_cases h2 : i.val<96
          · exact betaKernelForwardChecked002 i (Nat.le_of_not_gt h1) h2
          ·
            by_cases h3 : i.val<128
            · exact betaKernelForwardChecked003 i (Nat.le_of_not_gt h2) h3
            ·
              by_cases h4 : i.val<160
              · exact betaKernelForwardChecked004 i (Nat.le_of_not_gt h3) h4
              ·
                by_cases h5 : i.val<192
                · exact betaKernelForwardChecked005 i (Nat.le_of_not_gt h4) h5
                ·
                  by_cases h6 : i.val<224
                  · exact betaKernelForwardChecked006 i (Nat.le_of_not_gt h5) h6
                  ·
                    exact betaKernelForwardChecked007 i (Nat.le_of_not_gt h6) i.isLt)
    (by
      intro i
      exact betaKernelBackwardChecked000 i (Nat.zero_le _) i.isLt)

end SymmetricSubgroupAsymptotics.BinaryChart16T1086
