import SymmetricSubgroupAsymptotics.CFSGOrthogonalDIndexTrialityD4NeighborAdjacency
import SymmetricSubgroupAsymptotics.CFSGOrthogonalDIndexTrialityD4BoundedPencil

/-! Every actual D4 neighbour flag has exactly q original planes.
The equivalence retains the specified original intersection line and
three-space, and its source deletes precisely the original root plane.
Thus the fibres really are q-cliques; they have not been collapsed. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGOrthogonalDIndexTrialityD4ResidualSpace
open CFSGOrthogonalDSerreMatrices CFSGOrthogonalDIndexBundledQuadratic
open CFSGOrthogonalDIndexTrialityD4LinePencil
variable (K : Type) [Field K]

abbrev NeighborFlagFiber (U : RootPoints K) (W : ThreeExtensions K) :=
  {S : Neighbors K // neighborPoint K S = U ∧ neighborThreeSpace K S = W}

def rootIntervalPlane (U : RootPoints K) (W : ThreeExtensions K) : PlaneInterval U.val W.val :=
  ⟨rootPlane K, rootPlane_finrank K, U.property.2, W.property.2.2⟩

theorem interval_neighbor_data (U : RootPoints K) (W : ThreeExtensions K)
    (S : PlaneInterval U.val W.val) (hne : S ≠ rootIntervalPlane K U W) :
    rootPlane K ⊓ S.val = U.val ∧ rootPlane K ⊔ S.val = W.val := by
  have hSR : S.val ≠ rootPlane K := fun h => hne (Subtype.ext h)
  have hUle : U.val ≤ rootPlane K ⊓ S.val := le_inf U.property.2 S.property.2.1
  have hlo := Submodule.finrank_mono hUle
  rw [U.property.1] at hlo
  have hhi : Module.finrank K ↥(rootPlane K ⊓ S.val) ≤ 1 := by
    have hb := Submodule.finrank_mono (inf_le_left : rootPlane K ⊓ S.val ≤ rootPlane K)
    rw [rootPlane_finrank] at hb
    by_contra hn
    have hd : Module.finrank K ↥(rootPlane K ⊓ S.val) = 2 := by omega
    have heR : rootPlane K ⊓ S.val = rootPlane K :=
      Submodule.eq_of_le_of_finrank_le inf_le_left (by rw [hd, rootPlane_finrank])
    have heS : rootPlane K ⊓ S.val = S.val :=
      Submodule.eq_of_le_of_finrank_le inf_le_right (by rw [hd, S.property.1])
    exact hSR (heS.symm.trans heR)
  have hd : Module.finrank K ↥(rootPlane K ⊓ S.val) = 1 := by omega
  have hInf : rootPlane K ⊓ S.val = U.val :=
    (Submodule.eq_of_le_of_finrank_le hUle (by rw [hd, U.property.1])).symm
  have hs := Submodule.finrank_sup_add_finrank_inf_eq (rootPlane K) S.val
  rw [rootPlane_finrank, S.property.1, hd] at hs
  have hSup : rootPlane K ⊔ S.val = W.val :=
    Submodule.eq_of_le_of_finrank_le (sup_le W.property.2.2 S.property.2.2)
      (by rw [W.property.1]; omega)
  exact ⟨hInf, hSup⟩

def pencilNeighbor (U : RootPoints K) (W : ThreeExtensions K)
    (S : {S : PlaneInterval U.val W.val // S ≠ rootIntervalPlane K U W}) :
    NeighborFlagFiber K U W := by
  have hi := (interval_neighbor_data K U W S.val S.property).1
  have hs := (interval_neighbor_data K U W S.val S.property).2
  have hd : Module.finrank K ↥(rootPlane K ⊓ S.val.val) = 1 := by
    rw [hi, U.property.1]
  have hz : ∀ x ∈ rootPlane K ⊔ S.val.val, splitQuadraticForm K 4 x = 0 := by
    intro x hx
    exact W.property.2.1 x ((sup_le W.property.2.2 S.val.property.2.2) hx)
  let N : Neighbors K := ⟨S.val.val, S.val.property.1, hd, hz⟩
  exact ⟨N, Subtype.ext hi, Subtype.ext hs⟩

def neighborPencil (U : RootPoints K) (W : ThreeExtensions K)
    (S : NeighborFlagFiber K U W) :
    {S : PlaneInterval U.val W.val // S ≠ rootIntervalPlane K U W} := by
  have hU := congrArg Subtype.val S.property.1
  have hW := congrArg Subtype.val S.property.2
  let P : PlaneInterval U.val W.val :=
    ⟨S.val.val, S.val.property.1, hU.ge.trans (neighbor_point_le K S.val),
      (neighbor_le_threeSpace K S.val).trans hW.le⟩
  refine ⟨P, ?_⟩
  intro he
  exact neighbor_ne_rootPlane K S.val (congrArg Subtype.val he)

def neighborFiberPencilEquiv (U : RootPoints K) (W : ThreeExtensions K) :
    NeighborFlagFiber K U W ≃
      {S : PlaneInterval U.val W.val // S ≠ rootIntervalPlane K U W} where
  toFun := neighborPencil K U W
  invFun := pencilNeighbor K U W
  left_inv S := by
    apply Subtype.ext
    apply Subtype.ext
    rfl
  right_inv S := by
    apply Subtype.ext
    apply Subtype.ext
    rfl

theorem neighborFlagFiber_card [Finite K] (U : RootPoints K) (W : ThreeExtensions K) :
    Nat.card (NeighborFlagFiber K U W) = Nat.card K := by
  exact (Nat.card_congr (neighborFiberPencilEquiv K U W)).trans
    (planeInterval_except_card U.val W.val (U.property.2.trans W.property.2.2)
      U.property.1 W.property.1 (rootIntervalPlane K U W))

theorem neighborFlagFiber_clique (U : RootPoints K) (W : ThreeExtensions K)
    (S T : NeighborFlagFiber K U W) (hne : S ≠ T) : NeighborAdjacent K S.val T.val := by
  apply adjacent_of_same_threeSpace K S.val T.val
  · exact fun h => hne (Subtype.ext h)
  · exact S.property.2.trans T.property.2.symm

end SymmetricSubgroupAsymptotics.CFSGOrthogonalDIndexTrialityD4ResidualSpace
