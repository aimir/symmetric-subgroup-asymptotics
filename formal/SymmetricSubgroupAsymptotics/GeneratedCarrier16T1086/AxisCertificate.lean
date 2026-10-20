import SymmetricSubgroupAsymptotics.GeneratedCarrier16T1086.AxisRows000

/-! Selected literal carrier data; all checks use the Lean kernel. -/
set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 100000
noncomputable section
namespace SymmetricSubgroupAsymptotics.BinaryChart16T1086

def axisCayley : FiniteCayleyCertificate axisGenerators 4 where
  elements := fun i => axisElement i
  identity := 0
  identity_eq := by decide +kernel
  next i j := (axisNextTable i)[j.val]!
  next_eq := by
    intro i
    exact axisNextChecked000 i (Nat.zero_le _) i.isLt
  words i := axisWordTable i
  words_eq := by
    intro i
    exact axisWordsChecked000 i (Nat.zero_le _) i.isLt

def axisCertificate := axisCayley

end SymmetricSubgroupAsymptotics.BinaryChart16T1086
