import SymmetricSubgroupAsymptotics.BinaryRegularEightNaturalRegistryCharts
import SymmetricSubgroupAsymptotics.BinaryCoordinateDisplacementCertificate

set_option autoImplicit false
set_option maxRecDepth 10000
set_option maxHeartbeats 1000000
noncomputable section
open scoped BigOperators Classical
namespace SymmetricSubgroupAsymptotics.BinaryRegularEightNaturalRegistry

def radicalBasisMasks (i : Fin 47) : Array ℕ :=
  (#[#[],#[129,65,33,17,9,5,3],#[135,75,51],#[135,85,45],#[135,102,30],#[153,75,45],#[170,75,30],#[204,45,30],#[153,85,51],#[153,85,51],#[153,75,45],#[135,85,45],#[135,75,51],#[255],#[170,75,30],#[135,102,30],#[255],#[255],#[204,45,30],#[255],#[255],#[255],#[255],#[],#[135,75,45,30],#[135,75,45,30],#[135,75,45,30],#[135,75,51],#[135,75,45,30],#[135,75,45,30],#[135,85,45],#[135,75,45,30],#[135,75,45,30],#[135,102,30],#[153,75,45],#[170,75,30],#[204,45,30],#[153,85,51],#[255],#[255],#[255],#[255],#[255],#[255],#[255],#[135,75,45,30],#[255]] : Array (Array ℕ))[i.val]!
def radicalDualMasks (i : Fin 47) : Array ℕ :=
  (#[#[],#[128,64,32,16,8,4,2],#[128,64,32],#[128,64,32],#[128,64,16],#[128,64,32],#[128,64,16],#[128,32,16],#[128,64,32],#[128,64,32],#[128,64,32],#[128,64,32],#[128,64,32],#[128],#[128,64,16],#[128,64,16],#[128],#[128],#[128,32,16],#[128],#[128],#[128],#[128],#[],#[128,64,32,16],#[128,64,32,16],#[128,64,32,16],#[128,64,32],#[128,64,32,16],#[128,64,32,16],#[128,64,32],#[128,64,32,16],#[128,64,32,16],#[128,64,16],#[128,64,32],#[128,64,16],#[128,32,16],#[128,64,32],#[128],#[128],#[128],#[128],#[128],#[128],#[128],#[128,64,32,16],#[128]] : Array (Array ℕ))[i.val]!
def displacementCoefficientMasks (i : Fin 47) (j : ℕ) : Array ℕ :=
  ((#[#[],#[#[1,0,0],#[9,2,1],#[11,2,1],#[9,0,1],#[1,0,1],#[33,1,0],#[1,1,0]],#[#[1,0,0],#[1,0,1],#[3,0,1]],#[#[1,0,0],#[3,0,1],#[1,0,1]],#[#[0,1,0],#[0,3,1],#[0,1,1]],#[#[1,0,0],#[1,1,0],#[3,1,0]],#[#[0,1,0],#[1,1,0],#[4,0,0]],#[#[4,1,0],#[5,1,0],#[4,0,0]],#[#[1,0,0],#[0,1,0],#[3,1,0]],#[#[1,0,0],#[3,1,0],#[1,1,0]],#[#[1,0,0],#[3,1,0],#[0,1,0]],#[#[6,0,0],#[4,0,2],#[6,0,2]],#[#[6,0,0],#[6,0,4],#[2,0,4]],#[#[0,1,0]],#[#[0,1,0],#[3,1,0],#[1,0,0]],#[#[2,2,0],#[2,0,2],#[2,2,2]],#[#[1,0,0]],#[#[1,0,0]],#[#[2,1,0],#[0,1,0],#[1,0,0]],#[#[1,0,0]],#[#[1,0,0]],#[#[0,1,0]],#[#[0,0,1]],#[],#[#[16,0,0],#[16,0,2],#[2,0,3],#[16,0,1]],#[#[1,0,0],#[8,2,0],#[11,2,0],#[8,0,0]],#[#[1,0,0],#[9,2,0],#[11,2,0],#[9,0,0]],#[#[1,0,0],#[1,0,1],#[3,0,1]],#[#[1,0,0],#[9,2,0],#[11,2,0],#[8,0,0]],#[#[1,0,0],#[9,2,0],#[10,2,0],#[9,0,0]],#[#[1,0,0],#[2,0,1],#[1,0,1]],#[#[0,1,0],#[8,2,0],#[10,2,0],#[8,1,0]],#[#[0,1,0],#[8,2,0],#[10,3,0],#[8,0,0]],#[#[0,1,0],#[2,0,1],#[0,1,1]],#[#[8,0,0],#[8,2,0],#[10,2,0]],#[#[10,2,0],#[8,2,0],#[8,0,0]],#[#[8,2,0],#[10,2,0],#[8,0,0]],#[#[8,0,0],#[0,2,0],#[2,2,0]],#[#[1,0,0]],#[#[1,0,0]],#[#[0,2,0]],#[#[2,0,0]],#[#[2,0,0]],#[#[2,0,0]],#[#[2,0,0]],#[#[32,0,0],#[40,2,0],#[10,2,0],#[40,0,0]],#[#[2,0,0]]] : Array (Array (Array ℕ)))[i.val]!)[j]!
def headCeiling : Fin 47 → ℕ := ![0,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,3,3]
def radicalChart0 : BinaryCoordinateSpace 8 0 :=
  binaryCoordinateSpaceOfMasks 8 0
    (fun j => (radicalBasisMasks 0)[j.val]!)
    (fun j => (radicalDualMasks 0)[j.val]!)
    (by decide +kernel)

def radicalChart1 : BinaryCoordinateSpace 8 7 :=
  binaryCoordinateSpaceOfMasks 8 7
    (fun j => (radicalBasisMasks 1)[j.val]!)
    (fun j => (radicalDualMasks 1)[j.val]!)
    (by decide +kernel)

def radicalChart2 : BinaryCoordinateSpace 8 3 :=
  binaryCoordinateSpaceOfMasks 8 3
    (fun j => (radicalBasisMasks 2)[j.val]!)
    (fun j => (radicalDualMasks 2)[j.val]!)
    (by decide +kernel)

def radicalChart3 : BinaryCoordinateSpace 8 3 :=
  binaryCoordinateSpaceOfMasks 8 3
    (fun j => (radicalBasisMasks 3)[j.val]!)
    (fun j => (radicalDualMasks 3)[j.val]!)
    (by decide +kernel)

def radicalChart4 : BinaryCoordinateSpace 8 3 :=
  binaryCoordinateSpaceOfMasks 8 3
    (fun j => (radicalBasisMasks 4)[j.val]!)
    (fun j => (radicalDualMasks 4)[j.val]!)
    (by decide +kernel)

def radicalChart5 : BinaryCoordinateSpace 8 3 :=
  binaryCoordinateSpaceOfMasks 8 3
    (fun j => (radicalBasisMasks 5)[j.val]!)
    (fun j => (radicalDualMasks 5)[j.val]!)
    (by decide +kernel)

def radicalChart6 : BinaryCoordinateSpace 8 3 :=
  binaryCoordinateSpaceOfMasks 8 3
    (fun j => (radicalBasisMasks 6)[j.val]!)
    (fun j => (radicalDualMasks 6)[j.val]!)
    (by decide +kernel)

def radicalChart7 : BinaryCoordinateSpace 8 3 :=
  binaryCoordinateSpaceOfMasks 8 3
    (fun j => (radicalBasisMasks 7)[j.val]!)
    (fun j => (radicalDualMasks 7)[j.val]!)
    (by decide +kernel)

def radicalChart8 : BinaryCoordinateSpace 8 3 :=
  binaryCoordinateSpaceOfMasks 8 3
    (fun j => (radicalBasisMasks 8)[j.val]!)
    (fun j => (radicalDualMasks 8)[j.val]!)
    (by decide +kernel)

def radicalChart9 : BinaryCoordinateSpace 8 3 :=
  binaryCoordinateSpaceOfMasks 8 3
    (fun j => (radicalBasisMasks 9)[j.val]!)
    (fun j => (radicalDualMasks 9)[j.val]!)
    (by decide +kernel)

def radicalChart10 : BinaryCoordinateSpace 8 3 :=
  binaryCoordinateSpaceOfMasks 8 3
    (fun j => (radicalBasisMasks 10)[j.val]!)
    (fun j => (radicalDualMasks 10)[j.val]!)
    (by decide +kernel)

def radicalChart11 : BinaryCoordinateSpace 8 3 :=
  binaryCoordinateSpaceOfMasks 8 3
    (fun j => (radicalBasisMasks 11)[j.val]!)
    (fun j => (radicalDualMasks 11)[j.val]!)
    (by decide +kernel)

def radicalChart12 : BinaryCoordinateSpace 8 3 :=
  binaryCoordinateSpaceOfMasks 8 3
    (fun j => (radicalBasisMasks 12)[j.val]!)
    (fun j => (radicalDualMasks 12)[j.val]!)
    (by decide +kernel)

def radicalChart13 : BinaryCoordinateSpace 8 1 :=
  binaryCoordinateSpaceOfMasks 8 1
    (fun j => (radicalBasisMasks 13)[j.val]!)
    (fun j => (radicalDualMasks 13)[j.val]!)
    (by decide +kernel)

def radicalChart14 : BinaryCoordinateSpace 8 3 :=
  binaryCoordinateSpaceOfMasks 8 3
    (fun j => (radicalBasisMasks 14)[j.val]!)
    (fun j => (radicalDualMasks 14)[j.val]!)
    (by decide +kernel)

def radicalChart15 : BinaryCoordinateSpace 8 3 :=
  binaryCoordinateSpaceOfMasks 8 3
    (fun j => (radicalBasisMasks 15)[j.val]!)
    (fun j => (radicalDualMasks 15)[j.val]!)
    (by decide +kernel)

def radicalChart16 : BinaryCoordinateSpace 8 1 :=
  binaryCoordinateSpaceOfMasks 8 1
    (fun j => (radicalBasisMasks 16)[j.val]!)
    (fun j => (radicalDualMasks 16)[j.val]!)
    (by decide +kernel)

def radicalChart17 : BinaryCoordinateSpace 8 1 :=
  binaryCoordinateSpaceOfMasks 8 1
    (fun j => (radicalBasisMasks 17)[j.val]!)
    (fun j => (radicalDualMasks 17)[j.val]!)
    (by decide +kernel)

def radicalChart18 : BinaryCoordinateSpace 8 3 :=
  binaryCoordinateSpaceOfMasks 8 3
    (fun j => (radicalBasisMasks 18)[j.val]!)
    (fun j => (radicalDualMasks 18)[j.val]!)
    (by decide +kernel)

def radicalChart19 : BinaryCoordinateSpace 8 1 :=
  binaryCoordinateSpaceOfMasks 8 1
    (fun j => (radicalBasisMasks 19)[j.val]!)
    (fun j => (radicalDualMasks 19)[j.val]!)
    (by decide +kernel)

def radicalChart20 : BinaryCoordinateSpace 8 1 :=
  binaryCoordinateSpaceOfMasks 8 1
    (fun j => (radicalBasisMasks 20)[j.val]!)
    (fun j => (radicalDualMasks 20)[j.val]!)
    (by decide +kernel)

def radicalChart21 : BinaryCoordinateSpace 8 1 :=
  binaryCoordinateSpaceOfMasks 8 1
    (fun j => (radicalBasisMasks 21)[j.val]!)
    (fun j => (radicalDualMasks 21)[j.val]!)
    (by decide +kernel)

def radicalChart22 : BinaryCoordinateSpace 8 1 :=
  binaryCoordinateSpaceOfMasks 8 1
    (fun j => (radicalBasisMasks 22)[j.val]!)
    (fun j => (radicalDualMasks 22)[j.val]!)
    (by decide +kernel)

def radicalChart23 : BinaryCoordinateSpace 8 0 :=
  binaryCoordinateSpaceOfMasks 8 0
    (fun j => (radicalBasisMasks 23)[j.val]!)
    (fun j => (radicalDualMasks 23)[j.val]!)
    (by decide +kernel)

def radicalChart24 : BinaryCoordinateSpace 8 4 :=
  binaryCoordinateSpaceOfMasks 8 4
    (fun j => (radicalBasisMasks 24)[j.val]!)
    (fun j => (radicalDualMasks 24)[j.val]!)
    (by decide +kernel)

def radicalChart25 : BinaryCoordinateSpace 8 4 :=
  binaryCoordinateSpaceOfMasks 8 4
    (fun j => (radicalBasisMasks 25)[j.val]!)
    (fun j => (radicalDualMasks 25)[j.val]!)
    (by decide +kernel)

def radicalChart26 : BinaryCoordinateSpace 8 4 :=
  binaryCoordinateSpaceOfMasks 8 4
    (fun j => (radicalBasisMasks 26)[j.val]!)
    (fun j => (radicalDualMasks 26)[j.val]!)
    (by decide +kernel)

def radicalChart27 : BinaryCoordinateSpace 8 3 :=
  binaryCoordinateSpaceOfMasks 8 3
    (fun j => (radicalBasisMasks 27)[j.val]!)
    (fun j => (radicalDualMasks 27)[j.val]!)
    (by decide +kernel)

def radicalChart28 : BinaryCoordinateSpace 8 4 :=
  binaryCoordinateSpaceOfMasks 8 4
    (fun j => (radicalBasisMasks 28)[j.val]!)
    (fun j => (radicalDualMasks 28)[j.val]!)
    (by decide +kernel)

def radicalChart29 : BinaryCoordinateSpace 8 4 :=
  binaryCoordinateSpaceOfMasks 8 4
    (fun j => (radicalBasisMasks 29)[j.val]!)
    (fun j => (radicalDualMasks 29)[j.val]!)
    (by decide +kernel)

def radicalChart30 : BinaryCoordinateSpace 8 3 :=
  binaryCoordinateSpaceOfMasks 8 3
    (fun j => (radicalBasisMasks 30)[j.val]!)
    (fun j => (radicalDualMasks 30)[j.val]!)
    (by decide +kernel)

def radicalChart31 : BinaryCoordinateSpace 8 4 :=
  binaryCoordinateSpaceOfMasks 8 4
    (fun j => (radicalBasisMasks 31)[j.val]!)
    (fun j => (radicalDualMasks 31)[j.val]!)
    (by decide +kernel)

def radicalChart32 : BinaryCoordinateSpace 8 4 :=
  binaryCoordinateSpaceOfMasks 8 4
    (fun j => (radicalBasisMasks 32)[j.val]!)
    (fun j => (radicalDualMasks 32)[j.val]!)
    (by decide +kernel)

def radicalChart33 : BinaryCoordinateSpace 8 3 :=
  binaryCoordinateSpaceOfMasks 8 3
    (fun j => (radicalBasisMasks 33)[j.val]!)
    (fun j => (radicalDualMasks 33)[j.val]!)
    (by decide +kernel)

def radicalChart34 : BinaryCoordinateSpace 8 3 :=
  binaryCoordinateSpaceOfMasks 8 3
    (fun j => (radicalBasisMasks 34)[j.val]!)
    (fun j => (radicalDualMasks 34)[j.val]!)
    (by decide +kernel)

def radicalChart35 : BinaryCoordinateSpace 8 3 :=
  binaryCoordinateSpaceOfMasks 8 3
    (fun j => (radicalBasisMasks 35)[j.val]!)
    (fun j => (radicalDualMasks 35)[j.val]!)
    (by decide +kernel)

def radicalChart36 : BinaryCoordinateSpace 8 3 :=
  binaryCoordinateSpaceOfMasks 8 3
    (fun j => (radicalBasisMasks 36)[j.val]!)
    (fun j => (radicalDualMasks 36)[j.val]!)
    (by decide +kernel)

def radicalChart37 : BinaryCoordinateSpace 8 3 :=
  binaryCoordinateSpaceOfMasks 8 3
    (fun j => (radicalBasisMasks 37)[j.val]!)
    (fun j => (radicalDualMasks 37)[j.val]!)
    (by decide +kernel)

def radicalChart38 : BinaryCoordinateSpace 8 1 :=
  binaryCoordinateSpaceOfMasks 8 1
    (fun j => (radicalBasisMasks 38)[j.val]!)
    (fun j => (radicalDualMasks 38)[j.val]!)
    (by decide +kernel)

def radicalChart39 : BinaryCoordinateSpace 8 1 :=
  binaryCoordinateSpaceOfMasks 8 1
    (fun j => (radicalBasisMasks 39)[j.val]!)
    (fun j => (radicalDualMasks 39)[j.val]!)
    (by decide +kernel)

def radicalChart40 : BinaryCoordinateSpace 8 1 :=
  binaryCoordinateSpaceOfMasks 8 1
    (fun j => (radicalBasisMasks 40)[j.val]!)
    (fun j => (radicalDualMasks 40)[j.val]!)
    (by decide +kernel)

def radicalChart41 : BinaryCoordinateSpace 8 1 :=
  binaryCoordinateSpaceOfMasks 8 1
    (fun j => (radicalBasisMasks 41)[j.val]!)
    (fun j => (radicalDualMasks 41)[j.val]!)
    (by decide +kernel)

def radicalChart42 : BinaryCoordinateSpace 8 1 :=
  binaryCoordinateSpaceOfMasks 8 1
    (fun j => (radicalBasisMasks 42)[j.val]!)
    (fun j => (radicalDualMasks 42)[j.val]!)
    (by decide +kernel)

def radicalChart43 : BinaryCoordinateSpace 8 1 :=
  binaryCoordinateSpaceOfMasks 8 1
    (fun j => (radicalBasisMasks 43)[j.val]!)
    (fun j => (radicalDualMasks 43)[j.val]!)
    (by decide +kernel)

def radicalChart44 : BinaryCoordinateSpace 8 1 :=
  binaryCoordinateSpaceOfMasks 8 1
    (fun j => (radicalBasisMasks 44)[j.val]!)
    (fun j => (radicalDualMasks 44)[j.val]!)
    (by decide +kernel)

def radicalChart45 : BinaryCoordinateSpace 8 4 :=
  binaryCoordinateSpaceOfMasks 8 4
    (fun j => (radicalBasisMasks 45)[j.val]!)
    (fun j => (radicalDualMasks 45)[j.val]!)
    (by decide +kernel)

def radicalChart46 : BinaryCoordinateSpace 8 1 :=
  binaryCoordinateSpaceOfMasks 8 1
    (fun j => (radicalBasisMasks 46)[j.val]!)
    (fun j => (radicalDualMasks 46)[j.val]!)
    (by decide +kernel)

def radicalCharts (i : Fin 47) : Σ n, BinaryCoordinateSpace 8 n :=
  if i.val = 0 then ⟨0, radicalChart0⟩
  else if i.val = 1 then ⟨7, radicalChart1⟩
  else if i.val = 2 then ⟨3, radicalChart2⟩
  else if i.val = 3 then ⟨3, radicalChart3⟩
  else if i.val = 4 then ⟨3, radicalChart4⟩
  else if i.val = 5 then ⟨3, radicalChart5⟩
  else if i.val = 6 then ⟨3, radicalChart6⟩
  else if i.val = 7 then ⟨3, radicalChart7⟩
  else if i.val = 8 then ⟨3, radicalChart8⟩
  else if i.val = 9 then ⟨3, radicalChart9⟩
  else if i.val = 10 then ⟨3, radicalChart10⟩
  else if i.val = 11 then ⟨3, radicalChart11⟩
  else if i.val = 12 then ⟨3, radicalChart12⟩
  else if i.val = 13 then ⟨1, radicalChart13⟩
  else if i.val = 14 then ⟨3, radicalChart14⟩
  else if i.val = 15 then ⟨3, radicalChart15⟩
  else if i.val = 16 then ⟨1, radicalChart16⟩
  else if i.val = 17 then ⟨1, radicalChart17⟩
  else if i.val = 18 then ⟨3, radicalChart18⟩
  else if i.val = 19 then ⟨1, radicalChart19⟩
  else if i.val = 20 then ⟨1, radicalChart20⟩
  else if i.val = 21 then ⟨1, radicalChart21⟩
  else if i.val = 22 then ⟨1, radicalChart22⟩
  else if i.val = 23 then ⟨0, radicalChart23⟩
  else if i.val = 24 then ⟨4, radicalChart24⟩
  else if i.val = 25 then ⟨4, radicalChart25⟩
  else if i.val = 26 then ⟨4, radicalChart26⟩
  else if i.val = 27 then ⟨3, radicalChart27⟩
  else if i.val = 28 then ⟨4, radicalChart28⟩
  else if i.val = 29 then ⟨4, radicalChart29⟩
  else if i.val = 30 then ⟨3, radicalChart30⟩
  else if i.val = 31 then ⟨4, radicalChart31⟩
  else if i.val = 32 then ⟨4, radicalChart32⟩
  else if i.val = 33 then ⟨3, radicalChart33⟩
  else if i.val = 34 then ⟨3, radicalChart34⟩
  else if i.val = 35 then ⟨3, radicalChart35⟩
  else if i.val = 36 then ⟨3, radicalChart36⟩
  else if i.val = 37 then ⟨3, radicalChart37⟩
  else if i.val = 38 then ⟨1, radicalChart38⟩
  else if i.val = 39 then ⟨1, radicalChart39⟩
  else if i.val = 40 then ⟨1, radicalChart40⟩
  else if i.val = 41 then ⟨1, radicalChart41⟩
  else if i.val = 42 then ⟨1, radicalChart42⟩
  else if i.val = 43 then ⟨1, radicalChart43⟩
  else if i.val = 44 then ⟨1, radicalChart44⟩
  else if i.val = 45 then ⟨4, radicalChart45⟩
  else ⟨1, radicalChart46⟩
private theorem radical_basis_mem : ∀ i j,
  (radicalCharts i).2.inclusion (Pi.single j 1) ∈ (charts i).2.space := by decide +kernel
theorem radical_space_le_state (i : Fin 47) : (radicalCharts i).2.space ≤ (states i).toSubmodule :=
  (radicalCharts i).2.le_of_basis_mem _ (radical_basis_mem i)
def displacementVector (i : Fin 47) (j : Fin (radicalCharts i).1) (t : Fin 3) :
    (states i).toSubmodule :=
  ⟨(charts i).2.inclusion (binaryVectorOfMask _ ((displacementCoefficientMasks i j.val)[t.val]!)), ⟨_, rfl⟩⟩
private theorem radical_basis_eq : ∀ i j,
  (radicalCharts i).2.inclusion (Pi.single j 1) =
    ∑ t : Fin 3, (rho (generators t) (displacementVector i j t).val - (displacementVector i j t).val) := by decide +kernel
def radicalCertificate (i : Fin 47) :
    BinaryCoordinateDisplacementCertificate rho generators (states i) (radicalCharts i).2 where
  space_le_state := radical_space_le_state i
  termCount _ := 3
  termGenerator _ t := t
  termVector j t := displacementVector i j t
  basis_eq j := by
    apply Subtype.ext
    simpa only [Submodule.coe_sum] using radical_basis_eq i j
private theorem generator_basis_mem_radical : ∀ i g j,
  rho (generators g) ((charts i).2.inclusion (Pi.single j 1)) -
    (charts i).2.inclusion (Pi.single j 1) ∈ (radicalCharts i).2.space := by decide +kernel
theorem radical_eq_generatorDisplacementSpan (i : Fin 47) :
    representationGeneratorDisplacementSpan rho generators (states i) = (radicalCertificate i).submodule := by
  apply (radicalCertificate i).generatorDisplacementSpan_eq_of_basis_mem (charts i).2 (states_space i)
  intro g j
  change rho (generators g) ((charts i).2.inclusion (Pi.single j 1)) -
    (charts i).2.inclusion (Pi.single j 1) ∈ (radicalCharts i).2.space
  exact generator_basis_mem_radical i g j
theorem coinvariantsKer_map_eq_radical (i : Fin 47) :
    (Representation.Coinvariants.ker (states i).toRepresentation).map
      (states i).toSubmodule.subtype = (radicalCharts i).2.space := by
  rw [← representationGeneratorDisplacementSpan_eq_coinvariantsKer rho generators generators_full,
    radical_eq_generatorDisplacementSpan]
  exact (radicalCertificate i).submodule_map_subtype
private theorem codimension_le : ∀ i, (charts i).1 ≤ (radicalCharts i).1 + headCeiling i := by decide +kernel
theorem coinvariants_finrank_le (i : Fin 47) :
    Module.finrank (ZMod 2) (states i).toRepresentation.Coinvariants ≤ headCeiling i := by
  apply representationCoinvariants_finrank_le_of_displacementSubspace rho generators
    (states i) (radicalCertificate i).submodule (headCeiling i)
    (radicalCertificate i).le_generatorDisplacementSpan
  rw [(radicalCertificate i).finrank, states_space, (charts i).2.finrank]
  exact codimension_le i

end SymmetricSubgroupAsymptotics.BinaryRegularEightNaturalRegistry
