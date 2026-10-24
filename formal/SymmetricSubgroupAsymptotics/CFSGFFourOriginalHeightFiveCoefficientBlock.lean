import SymmetricSubgroupAsymptotics.CFSGFFourOriginalRootFamilyProfile
import SymmetricSubgroupAsymptotics.CFSGIntegralRootActionEntries

/-! One selected integral coefficient block for the whole-family source
certificate. It contains raises on height-three/four roots and lowerings
on height-four/five roots. The three certificates are finite integer
mixed identities at roots10,11,12. They do not by themselves assert the
new source actions; those require the checked height-induction theorem
and the full actual certificate assembly. -/
set_option autoImplicit false
set_option Elab.async false
namespace SymmetricSubgroupAsymptotics.CFSGFFourOriginalHeightFiveCoefficientBlock
open CFSGFFourOriginalRootFamilyProfile CFSGIntegralRootActionEntries

def zeroEntry : Slot×ℤ := (.inl 0,0)

def raisingEntry (i:Fin 4) : Slot→Slot×ℤ
  | .inr _=>zeroEntry
  | .inl k=>
    if k=7 then ![(.inl 11,-1),(.inl 10,-2),zeroEntry,zeroEntry] i else
    if k=8 then ![(.inl 12,1),zeroEntry,zeroEntry,(.inl 10,1)] i else
    if k=9 then ![zeroEntry,(.inl 12,1),zeroEntry,(.inl 11,1)] i else
    if k=10 then ![(.inl 14,1),zeroEntry,(.inl 13,1),zeroEntry] i else
    if k=11 then ![zeroEntry,(.inl 14,1),zeroEntry,zeroEntry] i else
    if k=12 then ![(.inl 15,2),zeroEntry,zeroEntry,(.inl 14,1)] i else zeroEntry

def loweringEntry (a:Fin 4) : Slot→Slot×ℤ
  | .inr _=>zeroEntry
  | .inl k=>
    if k=10 then ![zeroEntry,(.inl 7,-1),zeroEntry,(.inl 8,1)] a else
    if k=11 then ![(.inl 7,-1),zeroEntry,zeroEntry,(.inl 9,1)] a else
    if k=12 then ![(.inl 8,2),(.inl 9,1),zeroEntry,zeroEntry] a else
    if k=13 then ![zeroEntry,zeroEntry,(.inl 10,1),zeroEntry] a else
    if k=14 then ![(.inl 10,2),(.inl 11,1),zeroEntry,(.inl 12,1)] a else
    if k=15 then ![(.inl 12,1),zeroEntry,zeroEntry,zeroEntry] a else zeroEntry

def mixedIdentity (j:Slot) : Prop := ∀i a:Fin 4,
    (if a=i then (-integerWeight a j) • Pi.single j 1 else 0)+
      (loweringEntry a j).2 • integerRow (raisingEntry i (loweringEntry a j).1)=
      (raisingEntry i j).2 • integerRow (loweringEntry a (raisingEntry i j).1)

private theorem mixedIdentity_of_pointwise (j:Slot)
    (h:∀i a:Fin 4,∀k:Slot,
      (((if a=i then (-integerWeight a j) • Pi.single j 1 else 0)+
        (loweringEntry a j).2 • integerRow (raisingEntry i (loweringEntry a j).1):Slot→ℤ) k)=
        (((raisingEntry i j).2 • integerRow (loweringEntry a (raisingEntry i j).1):Slot→ℤ) k)) :
    mixedIdentity j := by
  intro i a
  exact funext (h i a)

theorem mixed_ten : mixedIdentity (.inl 10) := by
  apply mixedIdentity_of_pointwise
  decide +kernel

theorem mixed_eleven : mixedIdentity (.inl 11) := by
  apply mixedIdentity_of_pointwise
  decide +kernel

theorem mixed_twelve : mixedIdentity (.inl 12) := by
  apply mixedIdentity_of_pointwise
  decide +kernel

end SymmetricSubgroupAsymptotics.CFSGFFourOriginalHeightFiveCoefficientBlock
