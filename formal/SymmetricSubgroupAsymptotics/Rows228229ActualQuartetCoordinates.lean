import SymmetricSubgroupAsymptotics.BinaryThreeQuartetLiteralSocles
import SymmetricSubgroupAsymptotics.FunctionBlockOrbitProjectionIrreducibility
import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoTwelveTwistedAlternatingNaturalFamily
import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoTwelveDiagonalAlternatingNaturalFamily

/-! Two actual opposite-Singer three-quartet actions. All coordinates,
projector words, and finite local orbit witnesses retain original points. -/
set_option autoImplicit false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics.Rows228229ActualQuartetCoordinates
open SemidirectProduct BinaryPlanePermutationAffineEquiv BinaryPlaneWreathIrreducible
open Non2UnipotentPrefixFiniteMenu.PrimitiveAffineImprimitiveBlockTransfer.DegreeTwoTwelvePairFiniteCatalogue

def cycle : Equiv.Perm (Fin 3) := Equiv.swap 0 1 * Equiv.swap 1 2
abbrev Top := Subgroup.zpowers cycle
def mover : Top := ⟨cycle,Subgroup.mem_zpowers cycle⟩

def generators : Fin 2 → Fin 4 → Equiv.Perm (Fin 12) := ![row228Generators,row229Generators]
def topGenerator (j : Fin 4) : Top := if j = 3 then mover else 1
abbrev pointFrame : Fin 3 × Plane ≃ Fin 12 :=
  (Equiv.prodComm _ _).trans BinaryThreeQuartetLiteralSocles.pointChart

private def localPerm (r : Fin 2) (j : Fin 4) (i : Fin 3) : Equiv.Perm Plane where
  toFun v := (pointFrame.symm (generators r j
    (pointFrame ((topGenerator j)⁻¹ • i,v)))).2
  invFun v := (pointFrame.symm ((generators r j)⁻¹ (pointFrame (i,v)))).2
  left_inv := by revert r j i; decide +kernel
  right_inv := by revert r j i; decide +kernel

def lifted (r : Fin 2) (j : Fin 4) : BinaryThreeQuartetLiteralSocles.Model (R := Top) :=
  BinaryPlanePermutationWreathCoordinates.coordinates ⟨localPerm r j,topGenerator j⟩

theorem binding : ∀ (r : Fin 2) (j : Fin 4),
    BinaryThreeQuartetLiteralSocles.action (lifted r j) = generators r j := by
  decide +kernel

abbrev Actual (r : Fin 2) := Subgroup.closure (Set.range (lifted r))
abbrev LinearImage (r : Fin 2) := BinaryPlaneWreathNormalGenerators.actualImage (Actual r)
def linearGenerator (r : Fin 2) (j : Fin 4) : LinearImage r :=
  (IrreducibleAbelianSemidirectSubgroup.projection action (Actual r)).rangeRestrict
    (closureGenerators (lifted r) j)

def projector (r : Fin 2) (i : Fin 3) : LinearImage r :=
  let c := linearGenerator r 3
  let n := (i.val + 2) % 3
  c^n * linearGenerator r 2 * (c^n)⁻¹

def localWord (r : Fin 2) (i n : Fin 3) : LinearImage r :=
  projector r ⟨(i.val+1)%3,Nat.mod_lt _ (by decide)⟩ ^ n.val

private theorem projection_checked : ∀ (r : Fin 2) (i : Fin 3) (v : Fin 3 → V),
    v * restrictedAction (LinearImage r) (projector r i) v *
      restrictedAction (LinearImage r) ((projector r i)^2) v = Pi.mulSingle i (v i) := by
  decide +kernel
private theorem local_orbit_receipt : ∀ (r : Fin 2) (i : Fin 3) (v w : V),
    v ≠ 1 → w ≠ 1 →
    restrictedAction (LinearImage r) (localWord r i 0) (Pi.mulSingle i v) = Pi.mulSingle i w ∨
    restrictedAction (LinearImage r) (localWord r i 1) (Pi.mulSingle i v) = Pi.mulSingle i w ∨
    restrictedAction (LinearImage r) (localWord r i 2) (Pi.mulSingle i v) = Pi.mulSingle i w := by
  decide +kernel
private theorem local_orbit_checked : ∀ (r : Fin 2) (i : Fin 3) (v w : V),
    v ≠ 1 → w ≠ 1 → ∃ n : Fin 3,
      restrictedAction (LinearImage r) (localWord r i n) (Pi.mulSingle i v) = Pi.mulSingle i w := by
  intro r i v w hv hw
  rcases local_orbit_receipt r i v w hv hw with h | h | h
  · exact ⟨0,h⟩
  · exact ⟨1,h⟩
  · exact ⟨2,h⟩

def transport (r : Fin 2) (i j : Fin 3) : LinearImage r :=
  linearGenerator r 3 ^ ((j.val + 3 - i.val) % 3)
private theorem transport_checked : ∀ (r : Fin 2) (i j : Fin 3),
    ((transport r i j : LinearImage r) : W (R := Top) (I := Fin 3)).right • i = j := by
  decide +kernel

theorem irreducible (r : Fin 2) :
    IrreducibleAbelianSemidirect.Irreducible (restrictedAction (LinearImage r)) := by
  apply functionBlock_irreducible_of_three_term_projection_and_local_orbits
    (restrictedAction (LinearImage r)) ?_ ?_ (projector r) (projection_checked r)
  · intro i v w hv hw
    obtain ⟨n,hn⟩ := local_orbit_checked r i v w hv hw
    exact ⟨localWord r i n,hn⟩
  · intro i j
    let g := transport r i j
    refine ⟨g,localAction ((g : W (R := Top) (I := Fin 3)).left j),?_⟩
    intro v
    change action (g : W (R := Top) (I := Fin 3)) (Pi.mulSingle i v) = _
    rw [action_single,transport_checked]

end SymmetricSubgroupAsymptotics.Rows228229ActualQuartetCoordinates
