import SymmetricSubgroupAsymptotics.GeneratedKernelAxes.PilotBase077

set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
noncomputable section
namespace SymmetricSubgroupAsymptotics.BinaryKernelAxes077
local instance pilotChart001Group : Group Source := BinaryTopSource046.group

def chart1 : BinaryCoordinateSpace 8 1 where
  inclusion := Matrix.mulVecLin (fun i j => (((if i.val < 4 then (if i.val < 2 then (if i.val < 1 then #[1] else #[1]) else (if i.val < 3 then #[1] else #[1])) else (if i.val < 6 then (if i.val < 5 then #[1] else #[1]) else (if i.val < 7 then #[1] else #[1]))) : Array (ZMod 2))[j.val]!))
  coordinates := {
    toFun v j := v (7)
    map_add' _ _ := rfl
    map_smul' _ _ := rfl }
  left_inverse := by decide +kernel

private theorem positive1 : ∀ i j,
    action (generators i) (chart1.inclusion (Pi.single j 1))∈chart1.space := by
  simp only [action_numeric]
  decide +kernel
private theorem negative1 : ∀ i j,
    action (generators i)⁻¹ (chart1.inclusion (Pi.single j 1))∈chart1.space := by
  simp only [action_inverse_numeric]
  decide +kernel

def state1 : Subrepresentation action :=
  chart1.subrepresentationOfGenerators action generators generators_full positive1 negative1

end SymmetricSubgroupAsymptotics.BinaryKernelAxes077
