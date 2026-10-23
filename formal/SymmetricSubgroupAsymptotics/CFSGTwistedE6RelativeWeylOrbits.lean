import SymmetricSubgroupAsymptotics.CFSGTwistedE6WeylChamber
import SymmetricSubgroupAsymptotics.CFSGNormTwoCoordinateOrthogonalDescent
import SymmetricSubgroupAsymptotics.CFSGNormTwoCoordinateLatticeWord

/-! The four actual E6 diagram-orbit reflection words commute with the
diagram involution. A negative orbit strictly lowers the finite root
inversion count. Only four literal 6-by-6 involution identities are
checked finitely; no Weyl group or action table is enumerated. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Classical Matrix
namespace SymmetricSubgroupAsymptotics.CFSGTwistedE6RelativeWeylOrbits
open CFSGTwistedE6WeylChamber CFSGExceptionalNormTwoBases CFSGExceptionalCartanPositiveDefinite
open CFSGNormTwoRootPairing CFSGNormTwoGeckWeylWordDegree CFSGNormTwoGeckWeylLatticeLinear
open CFSGNormTwoCoordinateOrthogonalDescent CFSGNormTwoCoordinateInversionCount
open CFSGNormTwoCoordinateLatticeWord CFSGNormTwoCartanDiagramWords CFSGSerreDiagram

def orbitWord (a : Fin 4) : List (Fin 6) := ![[0,5],[2,4],[3],[1]] a

theorem orbitWord_nonempty (a : Fin 4) : 0<(orbitWord a).length := by
  fin_cases a <;> decide

theorem node_orbit_cover (i : Fin 6) :
    ∃a : Fin 4,∀j∈orbitWord a,j=i ∨ j=e6Permutation i := by
  fin_cases i
  · exact ⟨0,by decide⟩
  · exact ⟨3,by decide⟩
  · exact ⟨1,by decide⟩
  · exact ⟨2,by decide⟩
  · exact ⟨1,by decide⟩
  · exact ⟨0,by decide⟩

theorem orbit_root_commutes (a : Fin 4) (k : Roots CartanMatrix.E₆) :
    diagramRoot (CFSGTwistedE6WeylChamber.rootAction (orbitWord a) k)=
      CFSGTwistedE6WeylChamber.rootAction (orbitWord a) (diagramRoot k) := by
  have he := wordRoot_permutation CartanMatrix.E₆ CartanMatrix.E₆_diag CartanMatrix.E₆_transpose
    E6_positive_definite CartanMatrix.E₆_off_diag_nonpos e6Permutation e6_preserves (orbitWord a) k
  change diagramRoot (CFSGTwistedE6WeylChamber.rootAction (orbitWord a) k)=
    CFSGTwistedE6WeylChamber.rootAction ((orbitWord a).map e6Permutation) (diagramRoot k) at he
  rw [he]
  fin_cases a
  · change (E6Pairing.reflectionPerm (E6Index 5))
      ((E6Pairing.reflectionPerm (E6Index 0)) (diagramRoot k))=
        (E6Pairing.reflectionPerm (E6Index 0))
          ((E6Pairing.reflectionPerm (E6Index 5)) (diagramRoot k))
    exact congrArg (fun s : Equiv.Perm (Roots CartanMatrix.E₆)=>s (diagramRoot k))
      (orthogonal_reflections_commute CartanMatrix.E₆ CartanMatrix.E₆_diag
        CartanMatrix.E₆_transpose E6_positive_definite CartanMatrix.E₆_off_diag_nonpos
        0 5 (by decide) (by decide)).eq.symm
  · change (E6Pairing.reflectionPerm (E6Index 4))
      ((E6Pairing.reflectionPerm (E6Index 2)) (diagramRoot k))=
        (E6Pairing.reflectionPerm (E6Index 2))
          ((E6Pairing.reflectionPerm (E6Index 4)) (diagramRoot k))
    exact congrArg (fun s : Equiv.Perm (Roots CartanMatrix.E₆)=>s (diagramRoot k))
      (orthogonal_reflections_commute CartanMatrix.E₆ CartanMatrix.E₆_diag
        CartanMatrix.E₆_transpose E6_positive_definite CartanMatrix.E₆_off_diag_nonpos
        2 4 (by decide) (by decide)).eq.symm
  · rfl
  · rfl

theorem orbit_linear_square (a : Fin 4) : linearAction (orbitWord a)*linearAction (orbitWord a)=1 := by
  have hmat : ∀a : Fin 4,
      CFSGSignedCartanReflections.latticeWord CartanMatrix.E₆ (orbitWord a)*
        CFSGSignedCartanReflections.latticeWord CartanMatrix.E₆ (orbitWord a)=1 := by decide
  have hlin (x : Fin 6→ℤ) :
      CFSGSignedCartanReflections.latticeWord CartanMatrix.E₆ (orbitWord a)*ᵥx=
        linearAction (orbitWord a) x :=
    LinearMap.congr_fun (latticeWord_linear CartanMatrix.E₆ CartanMatrix.E₆_diag
      CartanMatrix.E₆_transpose E6_positive_definite CartanMatrix.E₆_off_diag_nonpos (orbitWord a)) x
  apply LinearEquiv.ext
  intro x
  change linearAction (orbitWord a) (linearAction (orbitWord a) x)=x
  rw [←hlin,←hlin,Matrix.mulVec_mulVec,hmat,Matrix.one_mulVec]

theorem exists_negative_orbit (w : List (Fin 6)) (hw : linearAction w≠1)
    (hcomm : ∀k,diagramRoot (CFSGTwistedE6WeylChamber.rootAction w k)=
      CFSGTwistedE6WeylChamber.rootAction w (diagramRoot k)) :
    ∃a : Fin 4,∀i∈orbitWord a,∀j,
      (CFSGTwistedE6WeylChamber.rootAction w (E6Index i)).val j≤0 := by
  obtain ⟨i,hi⟩ := exists_negative_simple w hw
  obtain ⟨a,ha⟩ := node_orbit_cover i
  refine ⟨a,?_⟩
  intro j hj
  rcases ha j hj with h|h
  · rw [h]
    exact hi
  · rw [h]
    exact negative_simple_partner w hcomm i hi

theorem negative_orbit_count_drop (w : List (Fin 6)) (a : Fin 4)
    (hneg : ∀i∈orbitWord a,∀j,(CFSGTwistedE6WeylChamber.rootAction w (E6Index i)).val j≤0) :
    inversionCount CartanMatrix.E₆ CartanMatrix.E₆_diag CartanMatrix.E₆_transpose
        E6_positive_definite CartanMatrix.E₆_off_diag_nonpos (w++orbitWord a)+(orbitWord a).length=
      inversionCount CartanMatrix.E₆ CartanMatrix.E₆_diag CartanMatrix.E₆_transpose
        E6_positive_definite CartanMatrix.E₆_off_diag_nonpos w := by
  fin_cases a
  · change inversionCount CartanMatrix.E₆ CartanMatrix.E₆_diag CartanMatrix.E₆_transpose E6_positive_definite CartanMatrix.E₆_off_diag_nonpos (w++[0,5])+2=inversionCount CartanMatrix.E₆ CartanMatrix.E₆_diag CartanMatrix.E₆_transpose E6_positive_definite CartanMatrix.E₆_off_diag_nonpos w
    exact inversionCount_append_pair CartanMatrix.E₆ CartanMatrix.E₆_diag CartanMatrix.E₆_transpose
      E6_positive_definite CartanMatrix.E₆_off_diag_nonpos w 0 5 (by decide)
      (hneg 0 (by decide)) (hneg 5 (by decide))
  · change inversionCount CartanMatrix.E₆ CartanMatrix.E₆_diag CartanMatrix.E₆_transpose E6_positive_definite CartanMatrix.E₆_off_diag_nonpos (w++[2,4])+2=inversionCount CartanMatrix.E₆ CartanMatrix.E₆_diag CartanMatrix.E₆_transpose E6_positive_definite CartanMatrix.E₆_off_diag_nonpos w
    exact inversionCount_append_pair CartanMatrix.E₆ CartanMatrix.E₆_diag CartanMatrix.E₆_transpose
      E6_positive_definite CartanMatrix.E₆_off_diag_nonpos w 2 4 (by decide)
      (hneg 2 (by decide)) (hneg 4 (by decide))
  · change inversionCount CartanMatrix.E₆ CartanMatrix.E₆_diag CartanMatrix.E₆_transpose E6_positive_definite CartanMatrix.E₆_off_diag_nonpos (w++[3])+1=inversionCount CartanMatrix.E₆ CartanMatrix.E₆_diag CartanMatrix.E₆_transpose E6_positive_definite CartanMatrix.E₆_off_diag_nonpos w
    exact inversionCount_append_simple CartanMatrix.E₆ CartanMatrix.E₆_diag CartanMatrix.E₆_transpose
      E6_positive_definite CartanMatrix.E₆_off_diag_nonpos w 3 (hneg 3 (by decide))
  · change inversionCount CartanMatrix.E₆ CartanMatrix.E₆_diag CartanMatrix.E₆_transpose E6_positive_definite CartanMatrix.E₆_off_diag_nonpos (w++[1])+1=inversionCount CartanMatrix.E₆ CartanMatrix.E₆_diag CartanMatrix.E₆_transpose E6_positive_definite CartanMatrix.E₆_off_diag_nonpos w
    exact inversionCount_append_simple CartanMatrix.E₆ CartanMatrix.E₆_diag CartanMatrix.E₆_transpose
      E6_positive_definite CartanMatrix.E₆_off_diag_nonpos w 1 (hneg 1 (by decide))

end SymmetricSubgroupAsymptotics.CFSGTwistedE6RelativeWeylOrbits
