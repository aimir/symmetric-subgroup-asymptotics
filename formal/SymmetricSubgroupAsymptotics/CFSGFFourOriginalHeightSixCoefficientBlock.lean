import SymmetricSubgroupAsymptotics.CFSGFFourOriginalHeightFiveCoefficientBlock

/-! A second selected sparse integral block. The new entries raise roots
13--15 and lower roots16--17; the adjacent rows come from the preceding
block. Pointwise integer certificates check the mixed identities on the
three height-five roots. These coefficients alone assert no source action;
the actual whole-family source induction must install them. -/
set_option autoImplicit false
set_option Elab.async false
namespace SymmetricSubgroupAsymptotics.CFSGFFourOriginalHeightSixCoefficientBlock
open CFSGFFourOriginalRootFamilyProfile CFSGIntegralRootActionEntries

private abbrev oldRaise := CFSGFFourOriginalHeightFiveCoefficientBlock.raisingEntry
private abbrev oldLower := CFSGFFourOriginalHeightFiveCoefficientBlock.loweringEntry
private abbrev zeroEntry := CFSGFFourOriginalHeightFiveCoefficientBlock.zeroEntry

def raisingEntry (i:Fin 4) : Slot→Slot×ℤ
  | .inr b=>oldRaise i (.inr b)
  | .inl k=>
    if k=13 then ![(.inl 16,1),zeroEntry,zeroEntry,zeroEntry] i else
    if k=14 then ![(.inl 17,2),zeroEntry,(.inl 16,1),zeroEntry] i else
    if k=15 then ![zeroEntry,zeroEntry,zeroEntry,(.inl 17,1)] i else oldRaise i (.inl k)

def loweringEntry (a:Fin 4) : Slot→Slot×ℤ
  | .inr b=>oldLower a (.inr b)
  | .inl k=>
    if k=16 then ![(.inl 13,2),zeroEntry,(.inl 14,1),zeroEntry] a else
    if k=17 then ![(.inl 14,1),zeroEntry,zeroEntry,(.inl 15,1)] a else oldLower a (.inl k)

def mixedIdentity (j:Slot) : Prop := ∀i a:Fin 4,
    (if a=i then (-integerWeight a j) • Pi.single j 1 else 0)+
      (loweringEntry a j).2 • integerRow (raisingEntry i (loweringEntry a j).1)=
      (raisingEntry i j).2 • integerRow (loweringEntry a (raisingEntry i j).1)

theorem mixed_thirteen : mixedIdentity (.inl 13) := by
  intro i a
  funext k
  revert i a k
  decide +kernel

theorem mixed_fourteen : mixedIdentity (.inl 14) := by
  intro i a
  funext k
  revert i a k
  decide +kernel

theorem mixed_fifteen : mixedIdentity (.inl 15) := by
  intro i a
  funext k
  revert i a k
  decide +kernel

private theorem height_five_indices : ∀j:Fin 24,rootHeight j=5→j=13∨j=14∨j=15 := by
  decide +kernel

theorem mixed_at_height_five (j:Fin 24) (hj:rootHeight j=5) : mixedIdentity (.inl j) := by
  rcases height_five_indices j hj with rfl|rfl|rfl
  · exact mixed_thirteen
  · exact mixed_fourteen
  · exact mixed_fifteen

end SymmetricSubgroupAsymptotics.CFSGFFourOriginalHeightSixCoefficientBlock
