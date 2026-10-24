import SymmetricSubgroupAsymptotics.CFSGFFourOriginalSimpleActionEntries
import SymmetricSubgroupAsymptotics.CFSGFFourOriginalHeightFiveCoefficientBlock

/-! The low-height sparse integer rows for the actual F4 source-family
certificate. They record the already established simple and height-two
through height-four coefficient conventions. The mixed certificates
are finite integer identities; installing the full source table still
requires the shared whole-family induction and the remaining blocks. -/
set_option autoImplicit false
set_option Elab.async false
namespace SymmetricSubgroupAsymptotics.CFSGFFourOriginalInitialCoefficientBlock
open CFSGFFourOriginalRootFamilyProfile CFSGIntegralRootActionEntries
open CFSGFFourOriginalSimpleActionEntries
private abbrev oldRaise := CFSGFFourOriginalHeightFiveCoefficientBlock.raisingEntry
private abbrev oldLower := CFSGFFourOriginalHeightFiveCoefficientBlock.loweringEntry
private abbrev zeroEntry := CFSGFFourOriginalHeightFiveCoefficientBlock.zeroEntry

def raisingEntry (i:Fin 4) : Slot→Slot×ℤ
  | .inr b=>cartanRaise i b
  | .inl k=>
    if k=0 then ![zeroEntry,zeroEntry,(.inl 4,-1),zeroEntry] i else
    if k=1 then ![zeroEntry,(.inl 5,-1),zeroEntry,(.inl 4,1)] i else
    if k=2 then ![(.inl 6,-1),zeroEntry,(.inl 5,1),zeroEntry] i else
    if k=3 then ![zeroEntry,(.inl 6,1),zeroEntry,zeroEntry] i else
    if k=4 then ![zeroEntry,(.inl 7,-1),zeroEntry,zeroEntry] i else
    if k=5 then ![(.inl 9,-1),(.inl 8,-2),zeroEntry,(.inl 7,1)] i else
    if k=6 then ![zeroEntry,zeroEntry,(.inl 9,1),zeroEntry] i else oldRaise i (.inl k)

def loweringEntry (a:Fin 4) : Slot→Slot×ℤ
  | .inr _=>zeroEntry
  | .inl k=>
    if k=0 then simpleLower a 3 else
    if k=1 then simpleLower a 2 else
    if k=2 then simpleLower a 1 else
    if k=3 then simpleLower a 0 else
    if k=4 then ![zeroEntry,zeroEntry,(.inl 0,-1),(.inl 1,1)] a else
    if k=5 then ![zeroEntry,(.inl 1,-2),(.inl 2,1),zeroEntry] a else
    if k=6 then ![(.inl 2,-1),(.inl 3,1),zeroEntry,zeroEntry] a else
    if k=7 then ![zeroEntry,(.inl 4,-2),zeroEntry,(.inl 5,1)] a else
    if k=8 then ![zeroEntry,(.inl 5,-1),zeroEntry,zeroEntry] a else
    if k=9 then ![(.inl 5,-1),zeroEntry,(.inl 6,1),zeroEntry] a else oldLower a (.inl k)

def mixedIdentity (j:Slot) : Prop := ∀i a:Fin 4,
    (if a=i then (-integerWeight a j) • Pi.single j 1 else 0)+
      (loweringEntry a j).2 • integerRow (raisingEntry i (loweringEntry a j).1)=
      (raisingEntry i j).2 • integerRow (loweringEntry a (raisingEntry i j).1)

private theorem mixed_pointwise_one : ∀j:Fin 24,rootHeight j=1→∀i a:Fin 4,∀k:Slot,
    (((if a=i then (-integerWeight a (.inl j)) • Pi.single (.inl j) 1 else 0)+
      (loweringEntry a (.inl j)).2 • integerRow
        (raisingEntry i (loweringEntry a (.inl j)).1):Slot→ℤ) k)=
    (((raisingEntry i (.inl j)).2 • integerRow
      (loweringEntry a (raisingEntry i (.inl j)).1):Slot→ℤ) k) := by decide +kernel

private theorem mixed_pointwise_two : ∀j:Fin 24,rootHeight j=2→∀i a:Fin 4,∀k:Slot,
    (((if a=i then (-integerWeight a (.inl j)) • Pi.single (.inl j) 1 else 0)+
      (loweringEntry a (.inl j)).2 • integerRow
        (raisingEntry i (loweringEntry a (.inl j)).1):Slot→ℤ) k)=
    (((raisingEntry i (.inl j)).2 • integerRow
      (loweringEntry a (raisingEntry i (.inl j)).1):Slot→ℤ) k) := by decide +kernel

private theorem mixed_pointwise_three : ∀j:Fin 24,rootHeight j=3→∀i a:Fin 4,∀k:Slot,
    (((if a=i then (-integerWeight a (.inl j)) • Pi.single (.inl j) 1 else 0)+
      (loweringEntry a (.inl j)).2 • integerRow
        (raisingEntry i (loweringEntry a (.inl j)).1):Slot→ℤ) k)=
    (((raisingEntry i (.inl j)).2 • integerRow
      (loweringEntry a (raisingEntry i (.inl j)).1):Slot→ℤ) k) := by decide +kernel

theorem mixed_at_height_one (j:Fin 24) (hj:rootHeight j=1) : mixedIdentity (.inl j) := by
  intro i a
  exact funext (mixed_pointwise_one j hj i a)

theorem mixed_at_height_two (j:Fin 24) (hj:rootHeight j=2) : mixedIdentity (.inl j) := by
  intro i a
  exact funext (mixed_pointwise_two j hj i a)

theorem mixed_at_height_three (j:Fin 24) (hj:rootHeight j=3) : mixedIdentity (.inl j) := by
  intro i a
  exact funext (mixed_pointwise_three j hj i a)

end SymmetricSubgroupAsymptotics.CFSGFFourOriginalInitialCoefficientBlock
