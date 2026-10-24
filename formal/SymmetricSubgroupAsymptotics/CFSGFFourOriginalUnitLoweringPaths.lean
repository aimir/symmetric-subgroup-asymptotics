import SymmetricSubgroupAsymptotics.CFSGFFourOriginalSignedSourceActions

/-! Unit-coefficient lowering paths for every displayed signed root.
These use the checked ORIGINAL source action table, rather than a matrix
orbit argument. In particular the doubled defining paths still have an
alternative unit lowering. Composing the corresponding integral matrix
adjoints with a simple coordinate will give integral root coordinates. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGFFourOriginalUnitLoweringPaths
open CFSG.Models.Chevalley CFSGFFourOriginalFiftyTwoFamily
open CFSGFFourOriginalRootFamilyProfile CFSGFFourOriginalSignedActionEntries
open CFSGFFourOriginalSignedSourceActions
local notation "A" => CartanMatrix.F₄

private def predecessor (j:Fin 24) : Fin 24:=
  ![0,1,2,3,1,2,3,5,5,6,8,9,9,10,11,12,14,14,16,16,18,20,21,22] j
private def loweringNode (j:Fin 24) : Fin 4:=
  ![0,0,0,0,3,2,1,3,1,2,3,3,1,2,1,0,2,0,1,0,0,1,2,3] j

private def stepsWithFuel : ℕ→Fin 24→List (Fin 4)
  | 0,_=>[]
  | n+1,j=>if j.val<4 then [] else loweringNode j::stepsWithFuel n (predecessor j)

def loweringSteps (j:Fin 24) : List (Fin 4):=stepsWithFuel 11 j

def terminalNode (j:Fin 24) : Fin 4:=
  ![3,2,1,0,2,1,0,1,1,0,1,0,0,1,0,0,0,0,0,0,0,0,0,0] j

def pathCoefficient (j:Fin 24) : ℤ:=if j=8∨j=10∨j=13 then -1 else 1

def entryPath (neg:Bool) : List (Fin 4)→BasisIndex→BasisIndex×ℤ
  | [],j=>(j,1)
  | i::ss,j=>
    let u:=signedEntry neg i j
    let v:=entryPath neg ss u.1
    (v.1,u.2*v.2)

theorem unit_path_certificate : ∀(neg:Bool)(j:Fin 24),
    entryPath (!neg) (loweringSteps j) (.inl (neg,j))=
      (.inl (neg,simpleIndex (terminalNode j)),pathCoefficient j) := by decide +kernel

theorem pathCoefficient_unit : ∀j:Fin 24,pathCoefficient j=1∨pathCoefficient j= -1 := by
  decide +kernel

def wordOperator (neg:Bool) : List (Fin 4)→Module.End ℚ (RationalLie A)
  | []=>1
  | i::ss=>wordOperator neg ss*LieAlgebra.ad ℚ (RationalLie A) (rootVector A neg i)

theorem word_action (neg:Bool) (ss:List (Fin 4)) (j:BasisIndex) :
    wordOperator neg ss (vectors j)=
      ((entryPath neg ss j).2:ℚ) • vectors (entryPath neg ss j).1 := by
  induction ss generalizing j with
  | nil=>simp only [wordOperator,Module.End.one_apply,entryPath,Int.cast_one,one_smul]
  | cons i ss ih=>
    change wordOperator neg ss ⁅rootVector A neg i,vectors j⁆=_
    rw [action,map_smul,ih,smul_smul]
    change (((signedEntry neg i j).2:ℚ)*((entryPath neg ss (signedEntry neg i j).1).2:ℚ)) •
      vectors (entryPath neg ss (signedEntry neg i j).1).1=
      (((signedEntry neg i j).2*(entryPath neg ss (signedEntry neg i j).1).2:ℤ):ℚ) •
      vectors (entryPath neg ss (signedEntry neg i j).1).1
    rw [Int.cast_mul]

theorem unit_lowering (neg:Bool) (j:Fin 24) :
    wordOperator (!neg) (loweringSteps j) (rootVectors neg j).val=
      (pathCoefficient j:ℚ) • rootVector A neg (terminalNode j) := by
  have h:=word_action (!neg) (loweringSteps j) (.inl (neg,j))
  rw [unit_path_certificate] at h
  change wordOperator (!neg) (loweringSteps j) (rootVectors neg j).val=
    (pathCoefficient j:ℚ) • family neg (.inl (simpleIndex (terminalNode j))) at h
  simpa only [simple_value] using h

end SymmetricSubgroupAsymptotics.CFSGFFourOriginalUnitLoweringPaths
