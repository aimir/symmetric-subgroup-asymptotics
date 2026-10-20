import SymmetricSubgroupAsymptotics.BinaryRegularEightNaturalRegistryData

set_option autoImplicit false
set_option maxRecDepth 10000
set_option maxHeartbeats 1000000
noncomputable section
open scoped BigOperators Classical
namespace SymmetricSubgroupAsymptotics.BinaryRegularEightNaturalRegistry

def chart0 : BinaryCoordinateSpace 8 0 :=
  binaryCoordinateSpaceOfMasks 8 0
    (fun j => (basisMasks 0)[j.val]!)
    (fun j => (dualMasks 0)[j.val]!)
    (by decide +kernel)

def chart1 : BinaryCoordinateSpace 8 8 :=
  binaryCoordinateSpaceOfMasks 8 8
    (fun j => (basisMasks 1)[j.val]!)
    (fun j => (dualMasks 1)[j.val]!)
    (by decide +kernel)

def chart2 : BinaryCoordinateSpace 8 4 :=
  binaryCoordinateSpaceOfMasks 8 4
    (fun j => (basisMasks 2)[j.val]!)
    (fun j => (dualMasks 2)[j.val]!)
    (by decide +kernel)

def chart3 : BinaryCoordinateSpace 8 4 :=
  binaryCoordinateSpaceOfMasks 8 4
    (fun j => (basisMasks 3)[j.val]!)
    (fun j => (dualMasks 3)[j.val]!)
    (by decide +kernel)

def chart4 : BinaryCoordinateSpace 8 4 :=
  binaryCoordinateSpaceOfMasks 8 4
    (fun j => (basisMasks 4)[j.val]!)
    (fun j => (dualMasks 4)[j.val]!)
    (by decide +kernel)

def chart5 : BinaryCoordinateSpace 8 4 :=
  binaryCoordinateSpaceOfMasks 8 4
    (fun j => (basisMasks 5)[j.val]!)
    (fun j => (dualMasks 5)[j.val]!)
    (by decide +kernel)

def chart6 : BinaryCoordinateSpace 8 4 :=
  binaryCoordinateSpaceOfMasks 8 4
    (fun j => (basisMasks 6)[j.val]!)
    (fun j => (dualMasks 6)[j.val]!)
    (by decide +kernel)

def chart7 : BinaryCoordinateSpace 8 4 :=
  binaryCoordinateSpaceOfMasks 8 4
    (fun j => (basisMasks 7)[j.val]!)
    (fun j => (dualMasks 7)[j.val]!)
    (by decide +kernel)

def chart8 : BinaryCoordinateSpace 8 4 :=
  binaryCoordinateSpaceOfMasks 8 4
    (fun j => (basisMasks 8)[j.val]!)
    (fun j => (dualMasks 8)[j.val]!)
    (by decide +kernel)

def chart9 : BinaryCoordinateSpace 8 4 :=
  binaryCoordinateSpaceOfMasks 8 4
    (fun j => (basisMasks 9)[j.val]!)
    (fun j => (dualMasks 9)[j.val]!)
    (by decide +kernel)

def chart10 : BinaryCoordinateSpace 8 4 :=
  binaryCoordinateSpaceOfMasks 8 4
    (fun j => (basisMasks 10)[j.val]!)
    (fun j => (dualMasks 10)[j.val]!)
    (by decide +kernel)

def chart11 : BinaryCoordinateSpace 8 4 :=
  binaryCoordinateSpaceOfMasks 8 4
    (fun j => (basisMasks 11)[j.val]!)
    (fun j => (dualMasks 11)[j.val]!)
    (by decide +kernel)

def chart12 : BinaryCoordinateSpace 8 4 :=
  binaryCoordinateSpaceOfMasks 8 4
    (fun j => (basisMasks 12)[j.val]!)
    (fun j => (dualMasks 12)[j.val]!)
    (by decide +kernel)

def chart13 : BinaryCoordinateSpace 8 2 :=
  binaryCoordinateSpaceOfMasks 8 2
    (fun j => (basisMasks 13)[j.val]!)
    (fun j => (dualMasks 13)[j.val]!)
    (by decide +kernel)

def chart14 : BinaryCoordinateSpace 8 4 :=
  binaryCoordinateSpaceOfMasks 8 4
    (fun j => (basisMasks 14)[j.val]!)
    (fun j => (dualMasks 14)[j.val]!)
    (by decide +kernel)

def chart15 : BinaryCoordinateSpace 8 4 :=
  binaryCoordinateSpaceOfMasks 8 4
    (fun j => (basisMasks 15)[j.val]!)
    (fun j => (dualMasks 15)[j.val]!)
    (by decide +kernel)

def chart16 : BinaryCoordinateSpace 8 2 :=
  binaryCoordinateSpaceOfMasks 8 2
    (fun j => (basisMasks 16)[j.val]!)
    (fun j => (dualMasks 16)[j.val]!)
    (by decide +kernel)

def chart17 : BinaryCoordinateSpace 8 2 :=
  binaryCoordinateSpaceOfMasks 8 2
    (fun j => (basisMasks 17)[j.val]!)
    (fun j => (dualMasks 17)[j.val]!)
    (by decide +kernel)

def chart18 : BinaryCoordinateSpace 8 4 :=
  binaryCoordinateSpaceOfMasks 8 4
    (fun j => (basisMasks 18)[j.val]!)
    (fun j => (dualMasks 18)[j.val]!)
    (by decide +kernel)

def chart19 : BinaryCoordinateSpace 8 2 :=
  binaryCoordinateSpaceOfMasks 8 2
    (fun j => (basisMasks 19)[j.val]!)
    (fun j => (dualMasks 19)[j.val]!)
    (by decide +kernel)

def chart20 : BinaryCoordinateSpace 8 2 :=
  binaryCoordinateSpaceOfMasks 8 2
    (fun j => (basisMasks 20)[j.val]!)
    (fun j => (dualMasks 20)[j.val]!)
    (by decide +kernel)

def chart21 : BinaryCoordinateSpace 8 2 :=
  binaryCoordinateSpaceOfMasks 8 2
    (fun j => (basisMasks 21)[j.val]!)
    (fun j => (dualMasks 21)[j.val]!)
    (by decide +kernel)

def chart22 : BinaryCoordinateSpace 8 2 :=
  binaryCoordinateSpaceOfMasks 8 2
    (fun j => (basisMasks 22)[j.val]!)
    (fun j => (dualMasks 22)[j.val]!)
    (by decide +kernel)

def chart23 : BinaryCoordinateSpace 8 1 :=
  binaryCoordinateSpaceOfMasks 8 1
    (fun j => (basisMasks 23)[j.val]!)
    (fun j => (dualMasks 23)[j.val]!)
    (by decide +kernel)

def chart24 : BinaryCoordinateSpace 8 6 :=
  binaryCoordinateSpaceOfMasks 8 6
    (fun j => (basisMasks 24)[j.val]!)
    (fun j => (dualMasks 24)[j.val]!)
    (by decide +kernel)

def chart25 : BinaryCoordinateSpace 8 6 :=
  binaryCoordinateSpaceOfMasks 8 6
    (fun j => (basisMasks 25)[j.val]!)
    (fun j => (dualMasks 25)[j.val]!)
    (by decide +kernel)

def chart26 : BinaryCoordinateSpace 8 6 :=
  binaryCoordinateSpaceOfMasks 8 6
    (fun j => (basisMasks 26)[j.val]!)
    (fun j => (dualMasks 26)[j.val]!)
    (by decide +kernel)

def chart27 : BinaryCoordinateSpace 8 5 :=
  binaryCoordinateSpaceOfMasks 8 5
    (fun j => (basisMasks 27)[j.val]!)
    (fun j => (dualMasks 27)[j.val]!)
    (by decide +kernel)

def chart28 : BinaryCoordinateSpace 8 6 :=
  binaryCoordinateSpaceOfMasks 8 6
    (fun j => (basisMasks 28)[j.val]!)
    (fun j => (dualMasks 28)[j.val]!)
    (by decide +kernel)

def chart29 : BinaryCoordinateSpace 8 6 :=
  binaryCoordinateSpaceOfMasks 8 6
    (fun j => (basisMasks 29)[j.val]!)
    (fun j => (dualMasks 29)[j.val]!)
    (by decide +kernel)

def chart30 : BinaryCoordinateSpace 8 5 :=
  binaryCoordinateSpaceOfMasks 8 5
    (fun j => (basisMasks 30)[j.val]!)
    (fun j => (dualMasks 30)[j.val]!)
    (by decide +kernel)

def chart31 : BinaryCoordinateSpace 8 6 :=
  binaryCoordinateSpaceOfMasks 8 6
    (fun j => (basisMasks 31)[j.val]!)
    (fun j => (dualMasks 31)[j.val]!)
    (by decide +kernel)

def chart32 : BinaryCoordinateSpace 8 6 :=
  binaryCoordinateSpaceOfMasks 8 6
    (fun j => (basisMasks 32)[j.val]!)
    (fun j => (dualMasks 32)[j.val]!)
    (by decide +kernel)

def chart33 : BinaryCoordinateSpace 8 5 :=
  binaryCoordinateSpaceOfMasks 8 5
    (fun j => (basisMasks 33)[j.val]!)
    (fun j => (dualMasks 33)[j.val]!)
    (by decide +kernel)

def chart34 : BinaryCoordinateSpace 8 5 :=
  binaryCoordinateSpaceOfMasks 8 5
    (fun j => (basisMasks 34)[j.val]!)
    (fun j => (dualMasks 34)[j.val]!)
    (by decide +kernel)

def chart35 : BinaryCoordinateSpace 8 5 :=
  binaryCoordinateSpaceOfMasks 8 5
    (fun j => (basisMasks 35)[j.val]!)
    (fun j => (dualMasks 35)[j.val]!)
    (by decide +kernel)

def chart36 : BinaryCoordinateSpace 8 5 :=
  binaryCoordinateSpaceOfMasks 8 5
    (fun j => (basisMasks 36)[j.val]!)
    (fun j => (dualMasks 36)[j.val]!)
    (by decide +kernel)

def chart37 : BinaryCoordinateSpace 8 5 :=
  binaryCoordinateSpaceOfMasks 8 5
    (fun j => (basisMasks 37)[j.val]!)
    (fun j => (dualMasks 37)[j.val]!)
    (by decide +kernel)

def chart38 : BinaryCoordinateSpace 8 3 :=
  binaryCoordinateSpaceOfMasks 8 3
    (fun j => (basisMasks 38)[j.val]!)
    (fun j => (dualMasks 38)[j.val]!)
    (by decide +kernel)

def chart39 : BinaryCoordinateSpace 8 3 :=
  binaryCoordinateSpaceOfMasks 8 3
    (fun j => (basisMasks 39)[j.val]!)
    (fun j => (dualMasks 39)[j.val]!)
    (by decide +kernel)

def chart40 : BinaryCoordinateSpace 8 3 :=
  binaryCoordinateSpaceOfMasks 8 3
    (fun j => (basisMasks 40)[j.val]!)
    (fun j => (dualMasks 40)[j.val]!)
    (by decide +kernel)

def chart41 : BinaryCoordinateSpace 8 3 :=
  binaryCoordinateSpaceOfMasks 8 3
    (fun j => (basisMasks 41)[j.val]!)
    (fun j => (dualMasks 41)[j.val]!)
    (by decide +kernel)

def chart42 : BinaryCoordinateSpace 8 3 :=
  binaryCoordinateSpaceOfMasks 8 3
    (fun j => (basisMasks 42)[j.val]!)
    (fun j => (dualMasks 42)[j.val]!)
    (by decide +kernel)

def chart43 : BinaryCoordinateSpace 8 3 :=
  binaryCoordinateSpaceOfMasks 8 3
    (fun j => (basisMasks 43)[j.val]!)
    (fun j => (dualMasks 43)[j.val]!)
    (by decide +kernel)

def chart44 : BinaryCoordinateSpace 8 3 :=
  binaryCoordinateSpaceOfMasks 8 3
    (fun j => (basisMasks 44)[j.val]!)
    (fun j => (dualMasks 44)[j.val]!)
    (by decide +kernel)

def chart45 : BinaryCoordinateSpace 8 7 :=
  binaryCoordinateSpaceOfMasks 8 7
    (fun j => (basisMasks 45)[j.val]!)
    (fun j => (dualMasks 45)[j.val]!)
    (by decide +kernel)

def chart46 : BinaryCoordinateSpace 8 4 :=
  binaryCoordinateSpaceOfMasks 8 4
    (fun j => (basisMasks 46)[j.val]!)
    (fun j => (dualMasks 46)[j.val]!)
    (by decide +kernel)

def charts (i : Fin 47) : Σ n, BinaryCoordinateSpace 8 n :=
  if i.val = 0 then ⟨0, chart0⟩
  else if i.val = 1 then ⟨8, chart1⟩
  else if i.val = 2 then ⟨4, chart2⟩
  else if i.val = 3 then ⟨4, chart3⟩
  else if i.val = 4 then ⟨4, chart4⟩
  else if i.val = 5 then ⟨4, chart5⟩
  else if i.val = 6 then ⟨4, chart6⟩
  else if i.val = 7 then ⟨4, chart7⟩
  else if i.val = 8 then ⟨4, chart8⟩
  else if i.val = 9 then ⟨4, chart9⟩
  else if i.val = 10 then ⟨4, chart10⟩
  else if i.val = 11 then ⟨4, chart11⟩
  else if i.val = 12 then ⟨4, chart12⟩
  else if i.val = 13 then ⟨2, chart13⟩
  else if i.val = 14 then ⟨4, chart14⟩
  else if i.val = 15 then ⟨4, chart15⟩
  else if i.val = 16 then ⟨2, chart16⟩
  else if i.val = 17 then ⟨2, chart17⟩
  else if i.val = 18 then ⟨4, chart18⟩
  else if i.val = 19 then ⟨2, chart19⟩
  else if i.val = 20 then ⟨2, chart20⟩
  else if i.val = 21 then ⟨2, chart21⟩
  else if i.val = 22 then ⟨2, chart22⟩
  else if i.val = 23 then ⟨1, chart23⟩
  else if i.val = 24 then ⟨6, chart24⟩
  else if i.val = 25 then ⟨6, chart25⟩
  else if i.val = 26 then ⟨6, chart26⟩
  else if i.val = 27 then ⟨5, chart27⟩
  else if i.val = 28 then ⟨6, chart28⟩
  else if i.val = 29 then ⟨6, chart29⟩
  else if i.val = 30 then ⟨5, chart30⟩
  else if i.val = 31 then ⟨6, chart31⟩
  else if i.val = 32 then ⟨6, chart32⟩
  else if i.val = 33 then ⟨5, chart33⟩
  else if i.val = 34 then ⟨5, chart34⟩
  else if i.val = 35 then ⟨5, chart35⟩
  else if i.val = 36 then ⟨5, chart36⟩
  else if i.val = 37 then ⟨5, chart37⟩
  else if i.val = 38 then ⟨3, chart38⟩
  else if i.val = 39 then ⟨3, chart39⟩
  else if i.val = 40 then ⟨3, chart40⟩
  else if i.val = 41 then ⟨3, chart41⟩
  else if i.val = 42 then ⟨3, chart42⟩
  else if i.val = 43 then ⟨3, chart43⟩
  else if i.val = 44 then ⟨3, chart44⟩
  else if i.val = 45 then ⟨7, chart45⟩
  else ⟨4, chart46⟩

private theorem positive : ∀ i g j,
  rho (generators g) ((charts i).2.inclusion (Pi.single j 1)) ∈ (charts i).2.space := by decide +kernel
private theorem negative : ∀ i g j,
  rho (generators g)⁻¹ ((charts i).2.inclusion (Pi.single j 1)) ∈ (charts i).2.space := by decide +kernel
def states (i : Fin 47) : Subrepresentation rho :=
  (charts i).2.subrepresentationOfGenerators rho generators generators_full (positive i) (negative i)
theorem states_space (i : Fin 47) : (states i).toSubmodule = (charts i).2.space := rfl
theorem bottom_space : (states 0).toSubmodule = ⊥ := by
  rw [states_space]
  change chart0.space = ⊥
  apply le_antisymm
  · rintro v ⟨a, rfl⟩
    change chart0.inclusion a = 0
    have ha : a = (0 : Fin 0 → ZMod 2) := Subsingleton.elim _ _
    rw [ha]
    exact chart0.inclusion.map_zero
  · exact bot_le

end SymmetricSubgroupAsymptotics.BinaryRegularEightNaturalRegistry
