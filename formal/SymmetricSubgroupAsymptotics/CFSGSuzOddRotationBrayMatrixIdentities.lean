import SymmetricSubgroupAsymptotics.CFSGSuzFirstSquareKroneckerPilot
import SymmetricSubgroupAsymptotics.CFSGSuzPackedBrayProductB2
import SymmetricSubgroupAsymptotics.CFSGSuzPackedBrayProductB3
import SymmetricSubgroupAsymptotics.CFSGSuzPackedBrayProductAB2
import SymmetricSubgroupAsymptotics.CFSGSuzPackedBrayProductAB2A
import SymmetricSubgroupAsymptotics.CFSGSuzPackedBrayProductR
import SymmetricSubgroupAsymptotics.CFSGSuzPackedBrayProductR2
import SymmetricSubgroupAsymptotics.CFSGSuzPackedBrayProductR4
import SymmetricSubgroupAsymptotics.CFSGSuzPackedBrayProductR8
import SymmetricSubgroupAsymptotics.CFSGSuzPackedBrayProductR12
import SymmetricSubgroupAsymptotics.CFSGSuzPackedBrayProductR14
import SymmetricSubgroupAsymptotics.CFSGSuzPackedBrayProductR15
import SymmetricSubgroupAsymptotics.CFSGSuzPackedBrayProductC
import SymmetricSubgroupAsymptotics.CFSGSuzPackedBrayProductC2
import SymmetricSubgroupAsymptotics.CFSGSuzPackedBrayProductC4

/-! Exact four whole-matrix identities for the original Suz arrays.
C256 is deduced algebraically from the stronger checked C4 identity. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGSuzOddRotationBrayMatrixIdentities
open CFSG.Models.MatrixGroups.Suz
private abbrev A := CFSG.Models.MatrixData.matrix 3 64 rows1
private abbrev B := CFSG.Models.MatrixData.matrix 3 64 rows2
private def r := A*B^2*A*B
private def c := r^8*B^2

private theorem b2_word : B^2=CFSGSuzPackedBrayProductB2.matrix := by rw [pow_two]; rfl

private theorem r_word : r=CFSGSuzPackedBrayProductR.matrix := by
  dsimp only [r]
  rw [b2_word]
  rfl

private theorem r2_word : r^2=CFSGSuzPackedBrayProductR2.matrix := by
  calc
    r^2=r*r := by rw [pow_two]
    _=CFSGSuzPackedBrayProductR2.matrix := by rw [r_word]; rfl

private theorem r4_word : r^4=CFSGSuzPackedBrayProductR4.matrix := by
  calc
    r^4=r^2*r^2 := by rw [←pow_add]
    _=CFSGSuzPackedBrayProductR4.matrix := by rw [r2_word]; rfl

private theorem r8_word : r^8=CFSGSuzPackedBrayProductR8.matrix := by
  calc
    r^8=r^4*r^4 := by rw [←pow_add]
    _=CFSGSuzPackedBrayProductR8.matrix := by rw [r4_word]; rfl

private theorem r12_word : r^12=CFSGSuzPackedBrayProductR12.matrix := by
  calc
    r^12=r^8*r^4 := by rw [←pow_add]
    _=CFSGSuzPackedBrayProductR12.matrix := by rw [r8_word,r4_word]; rfl

private theorem r14_word : r^14=CFSGSuzPackedBrayProductR14.matrix := by
  calc
    r^14=r^12*r^2 := by rw [←pow_add]
    _=CFSGSuzPackedBrayProductR14.matrix := by rw [r12_word,r2_word]; rfl

private theorem r15_word : r^15=CFSGSuzPackedBrayProductR15.matrix := by
  calc
    r^15=r^14*r := by rw [←pow_succ]
    _=CFSGSuzPackedBrayProductR15.matrix := by rw [r14_word,r_word]; rfl

private theorem c_word : c=CFSGSuzPackedBrayProductC.matrix := by
  dsimp only [c]
  rw [r8_word,b2_word]
  rfl

private theorem c2_word : c^2=CFSGSuzPackedBrayProductC2.matrix := by
  calc
    c^2=c*c := by rw [pow_two]
    _=CFSGSuzPackedBrayProductC2.matrix := by rw [c_word]; rfl

private theorem c4_word : c^4=CFSGSuzPackedBrayProductC4.matrix := by
  calc
    c^4=c^2*c^2 := by rw [←pow_add]
    _=CFSGSuzPackedBrayProductC4.matrix := by rw [c2_word]; rfl

theorem first_square : CFSG.Models.MatrixData.matrix 3 64 rows1^2=1 :=
  CFSGSuzFirstSquareKroneckerPilot.first_square

theorem second_cube : CFSG.Models.MatrixData.matrix 3 64 rows2^3=1 := by
  have he : B^3=CFSGSuzPackedBrayProductB3.matrix := by rw [pow_succ,b2_word]; rfl
  exact he.trans (CFSGSuzPackedBrayProductB3.cache.trans
    CFSGSuzFirstSquareKroneckerCaches.identity_cache_binding)

theorem rotation_fifteenth :
    (CFSG.Models.MatrixData.matrix 3 64 rows1*
      CFSG.Models.MatrixData.matrix 3 64 rows2^2*
      CFSG.Models.MatrixData.matrix 3 64 rows1*
      CFSG.Models.MatrixData.matrix 3 64 rows2)^15=1 :=
  r15_word.trans (CFSGSuzPackedBrayProductR15.cache.trans
    CFSGSuzFirstSquareKroneckerCaches.identity_cache_binding)

theorem bray_fourth : ((CFSG.Models.MatrixData.matrix 3 64 rows1*CFSG.Models.MatrixData.matrix 3 64 rows2^2*CFSG.Models.MatrixData.matrix 3 64 rows1*CFSG.Models.MatrixData.matrix 3 64 rows2)^8*CFSG.Models.MatrixData.matrix 3 64 rows2^2)^4=1 :=
  c4_word.trans (CFSGSuzPackedBrayProductC4.cache.trans
    CFSGSuzFirstSquareKroneckerCaches.identity_cache_binding)

theorem bray_binary_power : ((CFSG.Models.MatrixData.matrix 3 64 rows1*CFSG.Models.MatrixData.matrix 3 64 rows2^2*CFSG.Models.MatrixData.matrix 3 64 rows1*CFSG.Models.MatrixData.matrix 3 64 rows2)^8*CFSG.Models.MatrixData.matrix 3 64 rows2^2)^256=1 := by
  change c^256=1
  have hc : c^4=1 := bray_fourth
  calc
    c^256=(c^4)^64 := by rw [←pow_mul]
    _=1 := by rw [hc,one_pow]

end SymmetricSubgroupAsymptotics.CFSGSuzOddRotationBrayMatrixIdentities
