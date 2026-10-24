import SymmetricSubgroupAsymptotics.CFSGFFourOriginalHeightSixCoefficientBlock

/-! Sparse high-root integer data from individually selected candidates.
The first two mixed certificates check only the next height-six block.
All remaining rows are still data until the separate upper certificates
check them. No source action follows from the candidate discovery. -/
set_option autoImplicit false
set_option Elab.async false
namespace SymmetricSubgroupAsymptotics.CFSGFFourOriginalHighCoefficientBlock
open CFSGFFourOriginalRootFamilyProfile CFSGIntegralRootActionEntries
private abbrev oldRaise := CFSGFFourOriginalHeightSixCoefficientBlock.raisingEntry
private abbrev oldLower := CFSGFFourOriginalHeightSixCoefficientBlock.loweringEntry
private abbrev zeroEntry := CFSGFFourOriginalHeightFiveCoefficientBlock.zeroEntry

def raisingEntry (i:Fin 4) : Slot→Slot×ℤ
  | .inr b=>oldRaise i (.inr b)
  | .inl k=>
    if k=16 then ![(.inl 19,2),(.inl 18,1),zeroEntry,zeroEntry] i else
    if k=17 then ![zeroEntry,zeroEntry,(.inl 19,1),zeroEntry] i else
    if k=18 then ![(.inl 20,1),zeroEntry,zeroEntry,zeroEntry] i else
    if k=19 then ![zeroEntry,(.inl 20,1),zeroEntry,zeroEntry] i else
    if k=20 then ![zeroEntry,(.inl 21,2),zeroEntry,zeroEntry] i else
    if k=21 then ![zeroEntry,zeroEntry,(.inl 22,1),zeroEntry] i else
    if k=22 then ![zeroEntry,zeroEntry,zeroEntry,(.inl 23,1)] i else
    if k=23 then zeroEntry else oldRaise i (.inl k)

def loweringEntry (a:Fin 4) : Slot→Slot×ℤ
  | .inr b=>oldLower a (.inr b)
  | .inl k=>
    if k=18 then ![zeroEntry,(.inl 16,1),zeroEntry,zeroEntry] a else
    if k=19 then ![(.inl 16,1),zeroEntry,(.inl 17,1),zeroEntry] a else
    if k=20 then ![(.inl 18,1),(.inl 19,2),zeroEntry,zeroEntry] a else
    if k=21 then ![zeroEntry,(.inl 20,1),zeroEntry,zeroEntry] a else
    if k=22 then ![zeroEntry,zeroEntry,(.inl 21,1),zeroEntry] a else
    if k=23 then ![zeroEntry,zeroEntry,zeroEntry,(.inl 22,1)] a else oldLower a (.inl k)

def mixedIdentity (j:Slot) : Prop := ∀i a:Fin 4,
    (if a=i then (-integerWeight a j) • Pi.single j 1 else 0)+
      (loweringEntry a j).2 • integerRow (raisingEntry i (loweringEntry a j).1)=
      (raisingEntry i j).2 • integerRow (loweringEntry a (raisingEntry i j).1)

theorem mixed_sixteen : mixedIdentity (.inl 16) := by
  intro i a
  funext k
  revert i a k
  decide +kernel

theorem mixed_seventeen : mixedIdentity (.inl 17) := by
  intro i a
  funext k
  revert i a k
  decide +kernel

private theorem height_six_indices : ∀j:Fin 24,rootHeight j=6→j=16∨j=17 := by
  decide +kernel

theorem mixed_at_height_six (j:Fin 24) (hj:rootHeight j=6) : mixedIdentity (.inl j) := by
  rcases height_six_indices j hj with rfl|rfl
  · exact mixed_sixteen
  · exact mixed_seventeen

end SymmetricSubgroupAsymptotics.CFSGFFourOriginalHighCoefficientBlock
