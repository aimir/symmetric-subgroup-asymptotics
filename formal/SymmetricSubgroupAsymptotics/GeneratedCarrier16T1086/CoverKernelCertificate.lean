import SymmetricSubgroupAsymptotics.GeneratedCarrier16T1086.CoverKernelRows000

/-! Selected literal carrier data; all checks use the Lean kernel. -/
set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 100000
noncomputable section
namespace SymmetricSubgroupAsymptotics.BinaryChart16T1086

def coverKernelCayley : FiniteCayleyCertificate coverKernelGenerators 1 where
  elements := fun i => coverKernelElement i
  identity := 0
  identity_eq := by decide +kernel
  next i j := (coverKernelNextTable i)[j.val]!
  next_eq := by
    intro i
    exact coverKernelNextChecked000 i (Nat.zero_le _) i.isLt
  words i := coverKernelWordTable i
  words_eq := by
    intro i
    exact coverKernelWordsChecked000 i (Nat.zero_le _) i.isLt

def coverKernelCertificate := coverKernelCayley

end SymmetricSubgroupAsymptotics.BinaryChart16T1086
