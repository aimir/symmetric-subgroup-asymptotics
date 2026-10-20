import SymmetricSubgroupAsymptotics.GeneratedKernelAxes.PilotBase077

set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
noncomputable section
namespace SymmetricSubgroupAsymptotics.BinaryKernelAxes077
local instance pilotChart017Group : Group Source := BinaryTopSource046.group

def chart17 : BinaryCoordinateSpace 8 5 where
  inclusion := Matrix.mulVecLin (fun i j => (((if i.val < 4 then (if i.val < 2 then (if i.val < 1 then #[0,1,0,1,1] else #[1,0,0,1,1]) else (if i.val < 3 then #[1,0,0,0,0] else #[0,1,0,0,0])) else (if i.val < 6 then (if i.val < 5 then #[0,0,1,1,1] else #[0,0,1,0,0]) else (if i.val < 7 then #[0,0,0,1,0] else #[0,0,0,0,1]))) : Array (ZMod 2))[j.val]!))
  coordinates := {
    toFun v j := v ((if j.val < 2 then (if j.val < 1 then 2 else 3) else (if j.val < 3 then 5 else (if j.val < 4 then 6 else 7))))
    map_add' _ _ := rfl
    map_smul' _ _ := rfl }
  left_inverse := by decide +kernel

private theorem positive17 : ∀ i j,
    action (generators i) (chart17.inclusion (Pi.single j 1))∈chart17.space := by
  simp only [action_numeric]
  decide +kernel
private theorem negative17 : ∀ i j,
    action (generators i)⁻¹ (chart17.inclusion (Pi.single j 1))∈chart17.space := by
  simp only [action_inverse_numeric]
  decide +kernel

def state17 : Subrepresentation action :=
  chart17.subrepresentationOfGenerators action generators generators_full positive17 negative17

end SymmetricSubgroupAsymptotics.BinaryKernelAxes077
