import SymmetricSubgroupAsymptotics.CFSGTwistedE6HeisenbergStableRootFamilies
import SymmetricSubgroupAsymptotics.CFSGFFourE6PositiveSections
import SymmetricSubgroupAsymptotics.CFSGFFourE6DiagramFixed

/-! Four actual diagram-fixed complementary root pairs inside the
checked E6 configuration. Their standard Heisenberg cocycle survives in
all characteristics; unlike a paired diagram orbit it introduces no
factor2. Every selected fixed-root parameter is an ACTUAL folded F4
matrix, by the checked positive singleton section theorem. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics.CFSGFFourE6FixedHeisenbergPilot
open CFSGExceptionalHeisenbergRootPilot CFSGExceptionalCartanPositiveDefinite
open CFSGTwistedE6WeylChamber
open CFSGTwistedE6GeckDiagramCovariance CFSGTwistedE6GeckMatrixTwist
open CFSGNormTwoCoordinateSelectedRootElement CFSGFFourE6PositiveSections CFSGFFourE6DiagramFixed
local instance fFourHeisRootsDecidableEq : DecidableEq
    (CFSGNormTwoRootPairing.Roots CartanMatrix.E₆) := Classical.decEq _
private abbrev largerConfiguration := CFSGTwistedE6HeisenbergStableRootFamilies.configuration

def pick : Fin 4 → Fin 10 := ![0,1,5,7]

theorem pick_injective : Function.Injective pick := by decide

def configuration : RootConfig CartanMatrix.E₆ 4 where
  x i := largerConfiguration.x (pick i)
  y i := largerConfiguration.y (pick i)
  z := largerConfiguration.z
  head := largerConfiguration.head
  norm_x i := largerConfiguration.norm_x (pick i)
  norm_y i := largerConfiguration.norm_y (pick i)
  norm_z := largerConfiguration.norm_z
  positive_x i := largerConfiguration.positive_x (pick i)
  positive_y i := largerConfiguration.positive_y (pick i)
  positive_z := largerConfiguration.positive_z
  injective := by decide
  grade_x i := largerConfiguration.grade_x (pick i)
  grade_y i := largerConfiguration.grade_y (pick i)
  grade_z := largerConfiguration.grade_z
  sum i := largerConfiguration.sum (pick i)
  paired i := largerConfiguration.paired (pick i)
  within_x i j hij := largerConfiguration.within_x (pick i) (pick j) (fun he => hij (pick_injective he))
  within_y i j hij := largerConfiguration.within_y (pick i) (pick j) (fun he => hij (pick_injective he))
  cross i j hij := largerConfiguration.cross (pick i) (pick j) (fun he => hij (pick_injective he))
  central_x i := largerConfiguration.central_x (pick i)
  central_y i := largerConfiguration.central_y (pick i)

theorem diagram_first (i : Fin 4) :
    diagramRoot (configuration.xRoot i).val = (configuration.xRoot i).val := by
  change diagramRoot (largerConfiguration.xRoot (pick i)).val = (largerConfiguration.xRoot (pick i)).val
  have hi : CFSGTwistedE6HeisenbergStableRootFamilies.partner (pick i) = pick i := by
    fin_cases i <;> rfl
  exact (CFSGTwistedE6HeisenbergStableRootFamilies.diagram_first (pick i)).trans
    (congrArg (fun j : Fin 10 => (largerConfiguration.xRoot j).val) hi)

theorem diagram_second (i : Fin 4) :
    diagramRoot (configuration.yRoot i).val = (configuration.yRoot i).val := by
  change diagramRoot (largerConfiguration.yRoot (pick i)).val = (largerConfiguration.yRoot (pick i)).val
  have hi : CFSGTwistedE6HeisenbergStableRootFamilies.partner (pick i) = pick i := by
    fin_cases i <;> rfl
  exact (CFSGTwistedE6HeisenbergStableRootFamilies.diagram_second (pick i)).trans
    (congrArg (fun j : Fin 10 => (largerConfiguration.yRoot j).val) hi)

theorem diagram_central :
    diagramRoot configuration.zRoot.val = configuration.zRoot.val :=
  CFSGTwistedE6HeisenbergStableRootFamilies.diagram_central

theorem selected_fixed_parameter (K : Type) [Field K] [Finite K]
    (k : CFSGTwistedE6GeckOriginalRootSections.PositiveRoot)
    (hk : diagramRoot k.val = k.val) (a : K) :
    unitTwist K (RingEquiv.refl K)
      (selectedRootElement CartanMatrix.E₆ CartanMatrix.E₆_diag CartanMatrix.E₆_transpose
        E6_positive_definite CartanMatrix.E₆_off_diag_nonpos K k.val a) =
      selectedRootElement CartanMatrix.E₆ CartanMatrix.E₆_diag CartanMatrix.E₆_transpose
        E6_positive_definite CartanMatrix.E₆_off_diag_nonpos K k.val a := by
  let x : CFSGTwistedE6GeckSectionRootParameters.RootLine K k.val :=
    ⟨selectedRootElement CartanMatrix.E₆ CartanMatrix.E₆_diag CartanMatrix.E₆_transpose
      E6_positive_definite CartanMatrix.E₆_off_diag_nonpos K k.val a,
      selectedRootElement_mem CartanMatrix.E₆ CartanMatrix.E₆_diag CartanMatrix.E₆_transpose
        E6_positive_definite CartanMatrix.E₆_off_diag_nonpos K k.val a⟩
  exact foldedModel_le_diagramFixed K (singleton_root_mem_folded K k hk x)

end SymmetricSubgroupAsymptotics.CFSGFFourE6FixedHeisenbergPilot
