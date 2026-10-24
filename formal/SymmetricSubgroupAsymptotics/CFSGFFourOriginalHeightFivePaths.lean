import SymmetricSubgroupAsymptotics.CFSGSerreFiniteRootActionTable
import SymmetricSubgroupAsymptotics.CFSGFFourOriginalHeightFourLowering
import SymmetricSubgroupAsymptotics.CFSGSerreDividedPowers

/-! The three genuine parent paths into height five, including the
coefficient two supplied by the original divided-power multiplication
law. A first new lowering is installed by the shared coefficient-table
path theorem; no original basis or representation premise is used. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped BigOperators
namespace SymmetricSubgroupAsymptotics.CFSGFFourOriginalHeightFivePaths
open CFSG.Models.Chevalley CFSGSerreSignedRootWeights CFSGSerreFiniteRootActionTable
open CFSGSerreDividedPowers CFSGFFourOriginalFiftyTwoFamily
open CFSGFFourOriginalFirstLoweringComparison CFSGFFourOriginalHeightFourLowering
local notation "A" => CartanMatrix.F₄
local notation "L" => RationalLie A

theorem path_thirteen (neg:Bool) :
    (rootVectors neg 13).val=⁅rootVector A neg 2,(rootVectors neg 10).val⁆ := by
  change dividedPower A neg 2 1 (rootVectors neg 10).val=_
  simp [dividedPower]

theorem path_fourteen (neg:Bool) :
    (rootVectors neg 14).val=⁅rootVector A neg 3,(rootVectors neg 12).val⁆ := by
  change dividedPower A neg 3 1 (rootVectors neg 12).val=_
  simp [dividedPower]

theorem raising_zero_twelve (neg:Bool) :
    ⁅rootVector A neg 0,(rootVectors neg 12).val⁆=(2:ℚ) • (rootVectors neg 15).val := by
  have h:=congrArg (fun D:Module.End ℤ L=>D (rootVectors neg 8).val)
    (dividedPower_mul A neg 0 1 1)
  change dividedPower A neg 0 1 (dividedPower A neg 0 1 (rootVectors neg 8).val)=
    (2:ℕ) • dividedPower A neg 0 2 (rootVectors neg 8).val at h
  have h1:∀z:L,dividedPower A neg 0 1 z=⁅rootVector A neg 0,z⁆:=by
    intro z
    simp [dividedPower]
  simp only [h1] at h
  change ⁅rootVector A neg 0,⁅rootVector A neg 0,(rootVectors neg 8).val⁆⁆=
    (2:ℕ) • (rootVectors neg 15).val at h
  rw [←path_twelve] at h
  simpa only [two_smul] using h

theorem opposite_two_thirteen (neg:Bool) :
    ⁅oppositeVector A neg 2,(rootVectors neg 13).val⁆=(rootVectors neg 10).val := by
  let x:Fin 24→L:=fun j=>(rootVectors neg j).val
  have hc:simpleWeight (2:Fin 4) (10:Fin 24)= -1:=by decide +kernel
  have hw:⁅coroot A neg 2,x 10⁆=(-1:ℚ) • x 10 := by
    simpa only [x,hc,Int.cast_neg,Int.cast_one] using rootVectors_weight neg 2 10
  have hp:⁅rootVector A neg 2,x 10⁆=(1:ℚ) • (rootVectors neg 13).val := by
    rw [one_smul]
    exact (path_thirteen neg).symm
  have hd:⁅oppositeVector A neg 2,x 10⁆=
      Fintype.linearCombination ℚ x (0:Fin 24→ℚ) := by
    have h:=opposite_ten neg 2
    change ⁅oppositeVector A neg 2,(rootVectors neg 10).val⁆=0 at h
    simpa only [x,map_zero] using h
  have he:∀l,(0:Fin 24→ℚ) l≠0→⁅rootVector A neg 2,x l⁆=
      Fintype.linearCombination ℚ x (0:Fin 24→ℚ) := by
    intro l hl
    exact (hl rfl).elim
  have hcoeff:(if (2:Fin 4)=2 then (-(-1:ℚ)) • Pi.single (10:Fin 24) 1 else 0)+
      (∑l:Fin 24,(0:ℚ) • (0:Fin 24→ℚ))=(1:ℚ) • Pi.single (10:Fin 24) 1 := by
    simp
  have h:=lowering_of_raising_path A x neg 2 2 10 (-1) hw (rootVectors neg 13).val
    1 (by norm_num) hp 0 (fun _=>0) (Pi.single 10 1) hd he hcoeff
  simpa only [Fintype.linearCombination_apply_single,one_smul,x] using h

end SymmetricSubgroupAsymptotics.CFSGFFourOriginalHeightFivePaths
