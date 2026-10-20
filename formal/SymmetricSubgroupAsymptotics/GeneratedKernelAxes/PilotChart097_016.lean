import SymmetricSubgroupAsymptotics.GeneratedKernelAxes.PilotBase097

set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
noncomputable section
namespace SymmetricSubgroupAsymptotics.BinaryKernelAxes097
local instance pilotChart016Group : Group Source := BinaryTopSource056.group

def chart16 : BinaryCoordinateSpace 8 6 where
  inclusion := Matrix.mulVecLin (fun i j => (((if i.val < 4 then (if i.val < 2 then (if i.val < 1 then #[1,1,1,0,0,0] else #[1,0,0,0,0,0]) else (if i.val < 3 then #[0,1,0,0,0,0] else #[0,0,1,0,0,0])) else (if i.val < 6 then (if i.val < 5 then #[0,0,0,1,1,1] else #[0,0,0,1,0,0]) else (if i.val < 7 then #[0,0,0,0,1,0] else #[0,0,0,0,0,1]))) : Array (ZMod 2))[j.val]!))
  coordinates := {
    toFun v j := v ((if j.val < 3 then (if j.val < 1 then 1 else (if j.val < 2 then 2 else 3)) else (if j.val < 4 then 5 else (if j.val < 5 then 6 else 7))))
    map_add' _ _ := rfl
    map_smul' _ _ := rfl }
  left_inverse := by decide +kernel

private theorem positive16 : ∀ i j,
    action (generators i) (chart16.inclusion (Pi.single j 1))∈chart16.space := by
  simp only [action_numeric]
  decide +kernel
private theorem negative16 : ∀ i j,
    action (generators i)⁻¹ (chart16.inclusion (Pi.single j 1))∈chart16.space := by
  simp only [action_inverse_numeric]
  decide +kernel

def state16 : Subrepresentation action :=
  chart16.subrepresentationOfGenerators action generators generators_full positive16 negative16

end SymmetricSubgroupAsymptotics.BinaryKernelAxes097
