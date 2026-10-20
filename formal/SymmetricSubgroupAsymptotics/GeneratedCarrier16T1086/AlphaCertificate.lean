import SymmetricSubgroupAsymptotics.GeneratedCarrier16T1086.AlphaRows000
import SymmetricSubgroupAsymptotics.GeneratedCarrier16T1086.AlphaRows001
import SymmetricSubgroupAsymptotics.GeneratedCarrier16T1086.AlphaRows002
import SymmetricSubgroupAsymptotics.GeneratedCarrier16T1086.AlphaRows003
import SymmetricSubgroupAsymptotics.GeneratedCarrier16T1086.AlphaRows004
import SymmetricSubgroupAsymptotics.GeneratedCarrier16T1086.AlphaRows005
import SymmetricSubgroupAsymptotics.GeneratedCarrier16T1086.AlphaRows006
import SymmetricSubgroupAsymptotics.GeneratedCarrier16T1086.AlphaRows007
import SymmetricSubgroupAsymptotics.GeneratedCarrier16T1086.AlphaRows008
import SymmetricSubgroupAsymptotics.GeneratedCarrier16T1086.AlphaRows009
import SymmetricSubgroupAsymptotics.GeneratedCarrier16T1086.AlphaRows010
import SymmetricSubgroupAsymptotics.GeneratedCarrier16T1086.AlphaRows011
import SymmetricSubgroupAsymptotics.GeneratedCarrier16T1086.AlphaRows012
import SymmetricSubgroupAsymptotics.GeneratedCarrier16T1086.AlphaRows013
import SymmetricSubgroupAsymptotics.GeneratedCarrier16T1086.AlphaRows014
import SymmetricSubgroupAsymptotics.GeneratedCarrier16T1086.AlphaRows015
import SymmetricSubgroupAsymptotics.GeneratedCarrier16T1086.AlphaRows016
import SymmetricSubgroupAsymptotics.GeneratedCarrier16T1086.AlphaRows017
import SymmetricSubgroupAsymptotics.GeneratedCarrier16T1086.AlphaRows018
import SymmetricSubgroupAsymptotics.GeneratedCarrier16T1086.AlphaRows019
import SymmetricSubgroupAsymptotics.GeneratedCarrier16T1086.AlphaRows020
import SymmetricSubgroupAsymptotics.GeneratedCarrier16T1086.AlphaRows021
import SymmetricSubgroupAsymptotics.GeneratedCarrier16T1086.AlphaRows022
import SymmetricSubgroupAsymptotics.GeneratedCarrier16T1086.AlphaRows023
import SymmetricSubgroupAsymptotics.GeneratedCarrier16T1086.AlphaRows024
import SymmetricSubgroupAsymptotics.GeneratedCarrier16T1086.AlphaRows025
import SymmetricSubgroupAsymptotics.GeneratedCarrier16T1086.AlphaRows026
import SymmetricSubgroupAsymptotics.GeneratedCarrier16T1086.AlphaRows027
import SymmetricSubgroupAsymptotics.GeneratedCarrier16T1086.AlphaRows028
import SymmetricSubgroupAsymptotics.GeneratedCarrier16T1086.AlphaRows029
import SymmetricSubgroupAsymptotics.GeneratedCarrier16T1086.AlphaRows030
import SymmetricSubgroupAsymptotics.GeneratedCarrier16T1086.AlphaRows031

/-! Selected literal carrier data; all checks use the Lean kernel. -/
set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 100000
noncomputable section
namespace SymmetricSubgroupAsymptotics.BinaryChart16T1086

def alphaCayley : FiniteCayleyCertificate (fun j => (alphaGenerators j, alphaImages j)) 1024 where
  elements := fun i => (alphaSource i, alphaTarget i)
  identity := 0
  identity_eq := by decide +kernel
  next i j := (alphaNextTable i)[j.val]!
  next_eq := by
    intro i
    by_cases h0 : i.val<32
    · exact alphaNextChecked000 i (Nat.zero_le _) h0
    ·
      by_cases h1 : i.val<64
      · exact alphaNextChecked001 i (Nat.le_of_not_gt h0) h1
      ·
        by_cases h2 : i.val<96
        · exact alphaNextChecked002 i (Nat.le_of_not_gt h1) h2
        ·
          by_cases h3 : i.val<128
          · exact alphaNextChecked003 i (Nat.le_of_not_gt h2) h3
          ·
            by_cases h4 : i.val<160
            · exact alphaNextChecked004 i (Nat.le_of_not_gt h3) h4
            ·
              by_cases h5 : i.val<192
              · exact alphaNextChecked005 i (Nat.le_of_not_gt h4) h5
              ·
                by_cases h6 : i.val<224
                · exact alphaNextChecked006 i (Nat.le_of_not_gt h5) h6
                ·
                  by_cases h7 : i.val<256
                  · exact alphaNextChecked007 i (Nat.le_of_not_gt h6) h7
                  ·
                    by_cases h8 : i.val<288
                    · exact alphaNextChecked008 i (Nat.le_of_not_gt h7) h8
                    ·
                      by_cases h9 : i.val<320
                      · exact alphaNextChecked009 i (Nat.le_of_not_gt h8) h9
                      ·
                        by_cases h10 : i.val<352
                        · exact alphaNextChecked010 i (Nat.le_of_not_gt h9) h10
                        ·
                          by_cases h11 : i.val<384
                          · exact alphaNextChecked011 i (Nat.le_of_not_gt h10) h11
                          ·
                            by_cases h12 : i.val<416
                            · exact alphaNextChecked012 i (Nat.le_of_not_gt h11) h12
                            ·
                              by_cases h13 : i.val<448
                              · exact alphaNextChecked013 i (Nat.le_of_not_gt h12) h13
                              ·
                                by_cases h14 : i.val<480
                                · exact alphaNextChecked014 i (Nat.le_of_not_gt h13) h14
                                ·
                                  by_cases h15 : i.val<512
                                  · exact alphaNextChecked015 i (Nat.le_of_not_gt h14) h15
                                  ·
                                    by_cases h16 : i.val<544
                                    · exact alphaNextChecked016 i (Nat.le_of_not_gt h15) h16
                                    ·
                                      by_cases h17 : i.val<576
                                      · exact alphaNextChecked017 i (Nat.le_of_not_gt h16) h17
                                      ·
                                        by_cases h18 : i.val<608
                                        · exact alphaNextChecked018 i (Nat.le_of_not_gt h17) h18
                                        ·
                                          by_cases h19 : i.val<640
                                          · exact alphaNextChecked019 i (Nat.le_of_not_gt h18) h19
                                          ·
                                            by_cases h20 : i.val<672
                                            · exact alphaNextChecked020 i (Nat.le_of_not_gt h19) h20
                                            ·
                                              by_cases h21 : i.val<704
                                              · exact alphaNextChecked021 i (Nat.le_of_not_gt h20) h21
                                              ·
                                                by_cases h22 : i.val<736
                                                · exact alphaNextChecked022 i (Nat.le_of_not_gt h21) h22
                                                ·
                                                  by_cases h23 : i.val<768
                                                  · exact alphaNextChecked023 i (Nat.le_of_not_gt h22) h23
                                                  ·
                                                    by_cases h24 : i.val<800
                                                    · exact alphaNextChecked024 i (Nat.le_of_not_gt h23) h24
                                                    ·
                                                      by_cases h25 : i.val<832
                                                      · exact alphaNextChecked025 i (Nat.le_of_not_gt h24) h25
                                                      ·
                                                        by_cases h26 : i.val<864
                                                        · exact alphaNextChecked026 i (Nat.le_of_not_gt h25) h26
                                                        ·
                                                          by_cases h27 : i.val<896
                                                          · exact alphaNextChecked027 i (Nat.le_of_not_gt h26) h27
                                                          ·
                                                            by_cases h28 : i.val<928
                                                            · exact alphaNextChecked028 i (Nat.le_of_not_gt h27) h28
                                                            ·
                                                              by_cases h29 : i.val<960
                                                              · exact alphaNextChecked029 i (Nat.le_of_not_gt h28) h29
                                                              ·
                                                                by_cases h30 : i.val<992
                                                                · exact alphaNextChecked030 i (Nat.le_of_not_gt h29) h30
                                                                ·
                                                                  exact alphaNextChecked031 i (Nat.le_of_not_gt h30) i.isLt
  words i := alphaWordTable i
  words_eq := by
    intro i
    by_cases h0 : i.val<32
    · exact alphaWordsChecked000 i (Nat.zero_le _) h0
    ·
      by_cases h1 : i.val<64
      · exact alphaWordsChecked001 i (Nat.le_of_not_gt h0) h1
      ·
        by_cases h2 : i.val<96
        · exact alphaWordsChecked002 i (Nat.le_of_not_gt h1) h2
        ·
          by_cases h3 : i.val<128
          · exact alphaWordsChecked003 i (Nat.le_of_not_gt h2) h3
          ·
            by_cases h4 : i.val<160
            · exact alphaWordsChecked004 i (Nat.le_of_not_gt h3) h4
            ·
              by_cases h5 : i.val<192
              · exact alphaWordsChecked005 i (Nat.le_of_not_gt h4) h5
              ·
                by_cases h6 : i.val<224
                · exact alphaWordsChecked006 i (Nat.le_of_not_gt h5) h6
                ·
                  by_cases h7 : i.val<256
                  · exact alphaWordsChecked007 i (Nat.le_of_not_gt h6) h7
                  ·
                    by_cases h8 : i.val<288
                    · exact alphaWordsChecked008 i (Nat.le_of_not_gt h7) h8
                    ·
                      by_cases h9 : i.val<320
                      · exact alphaWordsChecked009 i (Nat.le_of_not_gt h8) h9
                      ·
                        by_cases h10 : i.val<352
                        · exact alphaWordsChecked010 i (Nat.le_of_not_gt h9) h10
                        ·
                          by_cases h11 : i.val<384
                          · exact alphaWordsChecked011 i (Nat.le_of_not_gt h10) h11
                          ·
                            by_cases h12 : i.val<416
                            · exact alphaWordsChecked012 i (Nat.le_of_not_gt h11) h12
                            ·
                              by_cases h13 : i.val<448
                              · exact alphaWordsChecked013 i (Nat.le_of_not_gt h12) h13
                              ·
                                by_cases h14 : i.val<480
                                · exact alphaWordsChecked014 i (Nat.le_of_not_gt h13) h14
                                ·
                                  by_cases h15 : i.val<512
                                  · exact alphaWordsChecked015 i (Nat.le_of_not_gt h14) h15
                                  ·
                                    by_cases h16 : i.val<544
                                    · exact alphaWordsChecked016 i (Nat.le_of_not_gt h15) h16
                                    ·
                                      by_cases h17 : i.val<576
                                      · exact alphaWordsChecked017 i (Nat.le_of_not_gt h16) h17
                                      ·
                                        by_cases h18 : i.val<608
                                        · exact alphaWordsChecked018 i (Nat.le_of_not_gt h17) h18
                                        ·
                                          by_cases h19 : i.val<640
                                          · exact alphaWordsChecked019 i (Nat.le_of_not_gt h18) h19
                                          ·
                                            by_cases h20 : i.val<672
                                            · exact alphaWordsChecked020 i (Nat.le_of_not_gt h19) h20
                                            ·
                                              by_cases h21 : i.val<704
                                              · exact alphaWordsChecked021 i (Nat.le_of_not_gt h20) h21
                                              ·
                                                by_cases h22 : i.val<736
                                                · exact alphaWordsChecked022 i (Nat.le_of_not_gt h21) h22
                                                ·
                                                  by_cases h23 : i.val<768
                                                  · exact alphaWordsChecked023 i (Nat.le_of_not_gt h22) h23
                                                  ·
                                                    by_cases h24 : i.val<800
                                                    · exact alphaWordsChecked024 i (Nat.le_of_not_gt h23) h24
                                                    ·
                                                      by_cases h25 : i.val<832
                                                      · exact alphaWordsChecked025 i (Nat.le_of_not_gt h24) h25
                                                      ·
                                                        by_cases h26 : i.val<864
                                                        · exact alphaWordsChecked026 i (Nat.le_of_not_gt h25) h26
                                                        ·
                                                          by_cases h27 : i.val<896
                                                          · exact alphaWordsChecked027 i (Nat.le_of_not_gt h26) h27
                                                          ·
                                                            by_cases h28 : i.val<928
                                                            · exact alphaWordsChecked028 i (Nat.le_of_not_gt h27) h28
                                                            ·
                                                              by_cases h29 : i.val<960
                                                              · exact alphaWordsChecked029 i (Nat.le_of_not_gt h28) h29
                                                              ·
                                                                by_cases h30 : i.val<992
                                                                · exact alphaWordsChecked030 i (Nat.le_of_not_gt h29) h30
                                                                ·
                                                                  exact alphaWordsChecked031 i (Nat.le_of_not_gt h30) i.isLt

def alphaCertificate : FiniteHomCertificate alphaGenerators alphaImages 1024 where
  cayley := alphaCayley
  first_kernel := by
    intro i
    by_cases h0 : i.val<32
    · exact alphaFirstKernelChecked000 i (Nat.zero_le _) h0
    ·
      by_cases h1 : i.val<64
      · exact alphaFirstKernelChecked001 i (Nat.le_of_not_gt h0) h1
      ·
        by_cases h2 : i.val<96
        · exact alphaFirstKernelChecked002 i (Nat.le_of_not_gt h1) h2
        ·
          by_cases h3 : i.val<128
          · exact alphaFirstKernelChecked003 i (Nat.le_of_not_gt h2) h3
          ·
            by_cases h4 : i.val<160
            · exact alphaFirstKernelChecked004 i (Nat.le_of_not_gt h3) h4
            ·
              by_cases h5 : i.val<192
              · exact alphaFirstKernelChecked005 i (Nat.le_of_not_gt h4) h5
              ·
                by_cases h6 : i.val<224
                · exact alphaFirstKernelChecked006 i (Nat.le_of_not_gt h5) h6
                ·
                  by_cases h7 : i.val<256
                  · exact alphaFirstKernelChecked007 i (Nat.le_of_not_gt h6) h7
                  ·
                    by_cases h8 : i.val<288
                    · exact alphaFirstKernelChecked008 i (Nat.le_of_not_gt h7) h8
                    ·
                      by_cases h9 : i.val<320
                      · exact alphaFirstKernelChecked009 i (Nat.le_of_not_gt h8) h9
                      ·
                        by_cases h10 : i.val<352
                        · exact alphaFirstKernelChecked010 i (Nat.le_of_not_gt h9) h10
                        ·
                          by_cases h11 : i.val<384
                          · exact alphaFirstKernelChecked011 i (Nat.le_of_not_gt h10) h11
                          ·
                            by_cases h12 : i.val<416
                            · exact alphaFirstKernelChecked012 i (Nat.le_of_not_gt h11) h12
                            ·
                              by_cases h13 : i.val<448
                              · exact alphaFirstKernelChecked013 i (Nat.le_of_not_gt h12) h13
                              ·
                                by_cases h14 : i.val<480
                                · exact alphaFirstKernelChecked014 i (Nat.le_of_not_gt h13) h14
                                ·
                                  by_cases h15 : i.val<512
                                  · exact alphaFirstKernelChecked015 i (Nat.le_of_not_gt h14) h15
                                  ·
                                    by_cases h16 : i.val<544
                                    · exact alphaFirstKernelChecked016 i (Nat.le_of_not_gt h15) h16
                                    ·
                                      by_cases h17 : i.val<576
                                      · exact alphaFirstKernelChecked017 i (Nat.le_of_not_gt h16) h17
                                      ·
                                        by_cases h18 : i.val<608
                                        · exact alphaFirstKernelChecked018 i (Nat.le_of_not_gt h17) h18
                                        ·
                                          by_cases h19 : i.val<640
                                          · exact alphaFirstKernelChecked019 i (Nat.le_of_not_gt h18) h19
                                          ·
                                            by_cases h20 : i.val<672
                                            · exact alphaFirstKernelChecked020 i (Nat.le_of_not_gt h19) h20
                                            ·
                                              by_cases h21 : i.val<704
                                              · exact alphaFirstKernelChecked021 i (Nat.le_of_not_gt h20) h21
                                              ·
                                                by_cases h22 : i.val<736
                                                · exact alphaFirstKernelChecked022 i (Nat.le_of_not_gt h21) h22
                                                ·
                                                  by_cases h23 : i.val<768
                                                  · exact alphaFirstKernelChecked023 i (Nat.le_of_not_gt h22) h23
                                                  ·
                                                    by_cases h24 : i.val<800
                                                    · exact alphaFirstKernelChecked024 i (Nat.le_of_not_gt h23) h24
                                                    ·
                                                      by_cases h25 : i.val<832
                                                      · exact alphaFirstKernelChecked025 i (Nat.le_of_not_gt h24) h25
                                                      ·
                                                        by_cases h26 : i.val<864
                                                        · exact alphaFirstKernelChecked026 i (Nat.le_of_not_gt h25) h26
                                                        ·
                                                          by_cases h27 : i.val<896
                                                          · exact alphaFirstKernelChecked027 i (Nat.le_of_not_gt h26) h27
                                                          ·
                                                            by_cases h28 : i.val<928
                                                            · exact alphaFirstKernelChecked028 i (Nat.le_of_not_gt h27) h28
                                                            ·
                                                              by_cases h29 : i.val<960
                                                              · exact alphaFirstKernelChecked029 i (Nat.le_of_not_gt h28) h29
                                                              ·
                                                                by_cases h30 : i.val<992
                                                                · exact alphaFirstKernelChecked030 i (Nat.le_of_not_gt h29) h30
                                                                ·
                                                                  exact alphaFirstKernelChecked031 i (Nat.le_of_not_gt h30) i.isLt

end SymmetricSubgroupAsymptotics.BinaryChart16T1086
