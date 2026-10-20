import SymmetricSubgroupAsymptotics.GeneratedKernelAxes.PilotBase077

set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
noncomputable section
namespace SymmetricSubgroupAsymptotics.BinaryKernelAxes077
local instance pilotChart003Group : Group Source := BinaryTopSource046.group

def chart3 : BinaryCoordinateSpace 8 2 where
  inclusion := Matrix.mulVecLin (fun i j => (((if i.val < 4 then (if i.val < 2 then (if i.val < 1 then #[0,1] else #[1,0]) else (if i.val < 3 then #[1,0] else #[0,1])) else (if i.val < 6 then (if i.val < 5 then #[1,0] else #[1,0]) else (if i.val < 7 then #[0,1] else #[0,1]))) : Array (ZMod 2))[j.val]!))
  coordinates := {
    toFun v j := v ((if j.val < 1 then 5 else 7))
    map_add' _ _ := rfl
    map_smul' _ _ := rfl }
  left_inverse := by decide +kernel

private theorem positive3 : ∀ i j,
    action (generators i) (chart3.inclusion (Pi.single j 1))∈chart3.space := by
  simp only [action_numeric]
  decide +kernel
private theorem negative3 : ∀ i j,
    action (generators i)⁻¹ (chart3.inclusion (Pi.single j 1))∈chart3.space := by
  simp only [action_inverse_numeric]
  decide +kernel

def state3 : Subrepresentation action :=
  chart3.subrepresentationOfGenerators action generators generators_full positive3 negative3

end SymmetricSubgroupAsymptotics.BinaryKernelAxes077
