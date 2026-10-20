import SymmetricSubgroupAsymptotics.GeneratedKernelAxes.PilotBase077

set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
noncomputable section
namespace SymmetricSubgroupAsymptotics.BinaryKernelAxes077
local instance pilotChart000Group : Group Source := BinaryTopSource046.group

def chart0 : BinaryCoordinateSpace 8 0 where
  inclusion := Matrix.mulVecLin (fun i j => (((if i.val < 4 then (if i.val < 2 then (if i.val < 1 then #[] else #[]) else (if i.val < 3 then #[] else #[])) else (if i.val < 6 then (if i.val < 5 then #[] else #[]) else (if i.val < 7 then #[] else #[]))) : Array (ZMod 2))[j.val]!))
  coordinates := {
    toFun v j := v (0)
    map_add' _ _ := rfl
    map_smul' _ _ := rfl }
  left_inverse := by decide +kernel

private theorem positive0 : ∀ i j,
    action (generators i) (chart0.inclusion (Pi.single j 1))∈chart0.space := by
  simp only [action_numeric]
  decide +kernel
private theorem negative0 : ∀ i j,
    action (generators i)⁻¹ (chart0.inclusion (Pi.single j 1))∈chart0.space := by
  simp only [action_inverse_numeric]
  decide +kernel

def state0 : Subrepresentation action :=
  chart0.subrepresentationOfGenerators action generators generators_full positive0 negative0

end SymmetricSubgroupAsymptotics.BinaryKernelAxes077
