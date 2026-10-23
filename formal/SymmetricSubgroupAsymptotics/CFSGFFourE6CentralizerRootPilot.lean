import SymmetricSubgroupAsymptotics.CFSGExceptionalGeckIntegralData
import SymmetricSubgroupAsymptotics.CFSGNormTwoCoordinatePositiveRootGenerators
import SymmetricSubgroupAsymptotics.CFSGTwistedE6DiagramRootOrthogonality

/-! A selected fifteen-root pilot, not an exhaustive E6 root census.
These are precisely the positive intervals in the literal A5 chain
0--2--3--4--5. They are orthogonal to the actual highest root and form
three singleton and six paired diagram orbits. The root and diagram
statements are over the integral lattice, before any field or F4 image
specialization, so the same geometry is available for twisted E6. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGFFourE6CentralizerRootPilot
open CFSGIntegerMatrixPairing CFSGNormTwoRootPairing
open CFSGNormTwoCoordinatePositiveRootGenerators CFSGTwistedE6WeylChamber
open CFSGTwistedE6DiagramRootOrthogonality CFSGSerreDiagram

private def rows : Fin 15 → Fin 6 → ℤ :=
  ![![1,0,0,0,0,0], ![0,0,1,0,0,0], ![0,0,0,1,0,0],
    ![0,0,0,0,1,0], ![0,0,0,0,0,1],
    ![1,0,1,0,0,0], ![0,0,1,1,0,0],
    ![0,0,0,1,1,0], ![0,0,0,0,1,1],
    ![1,0,1,1,0,0], ![0,0,1,1,1,0], ![0,0,0,1,1,1],
    ![1,0,1,1,1,0], ![0,0,1,1,1,1], ![1,0,1,1,1,1]]

private def highestRow : Fin 6 → ℤ := ![1,2,2,3,2,1]

private theorem rows_norm : ∀i,integerPairing CartanMatrix.E₆ (rows i) (rows i)=2 := by decide
private theorem rows_positive : ∀i j,0≤rows i j := by decide
private theorem rows_injective : Function.Injective rows := by decide
private theorem highest_norm : integerPairing CartanMatrix.E₆ highestRow highestRow=2 := by decide

def highestRoot : Roots CartanMatrix.E₆ := ⟨highestRow,highest_norm⟩

def intervalRoot (i : Fin 15) : PositiveRoot CartanMatrix.E₆ :=
  ⟨⟨rows i,rows_norm i⟩,rows_positive i⟩

def partner : Fin 15 → Fin 15 := ![4,3,2,1,0,8,7,6,5,11,10,9,13,12,14]

def representative : Fin 9 → Fin 15 := ![0,1,2,5,6,9,10,12,14]

theorem intervalRoot_injective : Function.Injective intervalRoot := by
  intro i j he
  exact rows_injective (congrArg (fun k : PositiveRoot CartanMatrix.E₆=>k.val.val) he)

theorem partner_involutive : Function.Involutive partner := by
  have h : ∀i : Fin 15,partner (partner i)=i := by decide
  exact h

theorem representative_injective : Function.Injective representative := by decide

theorem representative_orbits_disjoint (i j : Fin 9)
    (he : representative i=representative j ∨ representative i=partner (representative j)) :
    i=j := by
  have h : ∀i j : Fin 9,
      representative i=representative j ∨ representative i=partner (representative j) → i=j := by
    decide
  exact h i j he

theorem representative_orbits_cover (i : Fin 15) :
    ∃j : Fin 9,i=representative j ∨ i=partner (representative j) := by
  have h : ∀i : Fin 15,∃j : Fin 9,i=representative j ∨ i=partner (representative j) := by decide
  exact h i

theorem intervalRoot_orthogonal_highest (i : Fin 15) :
    integerPairing CartanMatrix.E₆ (intervalRoot i).val.val highestRoot.val=0 := by
  have h : ∀i,integerPairing CartanMatrix.E₆ (rows i) highestRow=0 := by decide
  exact h i

theorem intervalRoot_diagram (i : Fin 15) :
    diagramRoot (intervalRoot i).val=(intervalRoot (partner i)).val := by
  apply Subtype.ext
  funext j
  rw [diagramRoot_coordinate]
  have h : ∀i j,rows i (e6Permutation j)=rows (partner i) j := by decide
  exact h i j

theorem highestRoot_diagram : diagramRoot highestRoot=highestRoot := by
  apply Subtype.ext
  funext j
  rw [diagramRoot_coordinate]
  have h : ∀j,highestRow (e6Permutation j)=highestRow j := by decide
  exact h j

theorem representative_fixed_iff (j : Fin 9) :
    partner (representative j)=representative j ↔ j=2 ∨ j=6 ∨ j=8 := by
  have h : ∀j : Fin 9,partner (representative j)=representative j ↔ j=2 ∨ j=6 ∨ j=8 := by
    decide
  exact h j

end SymmetricSubgroupAsymptotics.CFSGFFourE6CentralizerRootPilot
