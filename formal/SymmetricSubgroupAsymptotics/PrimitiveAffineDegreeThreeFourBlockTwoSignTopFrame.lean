import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeThreeFourBlockTwoSignLiteralStructure
import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeThreeFourBlockSignedIsotypeSplit
import SymmetricSubgroupAsymptotics.TransitiveBinaryPairFrame
import SymmetricSubgroupAsymptotics.BinaryPairFrameGenerators

/-!
# The literal two-sign block system on the four-point top

The two-sign branch gives an equality partition of the four pair
coordinates into two classes.  This file descends the actual top action to
those two classes and builds the resulting binary pair frame on the
four-point top itself.

This is the structural form of the statement `T <= D8`: it retains the
literal top subgroup, the literal two sign classes, and the actual action on
those classes.  No representative from a transitive-group catalogue is
chosen.
-/

set_option autoImplicit false
noncomputable section
open scoped Classical

namespace SymmetricSubgroupAsymptotics
namespace BinaryPairFrame

variable {X : Type} {G : Subgroup (Equiv.Perm X)}
  (F : BinaryPairFrame G (Fin 4))

/-- Every pair frame embeds its source group in the full group preserving
that same literal pair partition. -/
def pairPreservingEmbedding {I : Type*} {H : Subgroup (Equiv.Perm X)}
    (D : BinaryPairFrame H I) : H →* pairPreserving D.frame where
  toFun h := ⟨h.1, ⟨D.top h, D.intertwine h⟩⟩
  map_one' := Subtype.ext rfl
  map_mul' _ _ := Subtype.ext rfl

theorem pairPreservingEmbedding_injective
    {I : Type*} {H : Subgroup (Equiv.Perm X)}
    (D : BinaryPairFrame H I) :
    Function.Injective (pairPreservingEmbedding D) := by
  intro a b h
  apply Subtype.ext
  exact congrArg (fun u : pairPreserving D.frame => (u.1 : Equiv.Perm X)) h

/-- A chosen coordinate carrying a realized literal sign. -/
noncomputable def fourCoordinateSignRepresentative
    (chi : FourCoordinateSign F) : Fin 4 :=
  Classical.choose chi.2

theorem fourCoordinateSignRepresentative_spec
    (chi : FourCoordinateSign F) :
    fourCoordinateSign F (fourCoordinateSignRepresentative F chi) = chi := by
  apply Subtype.ext
  exact Classical.choose_spec chi.2

/-- Transport a realized sign by an element of the actual pair action. -/
noncomputable def fourCoordinateSignTopMap
    (u : G) (chi : FourCoordinateSign F) : FourCoordinateSign F :=
  fourCoordinateSign F
    (F.top u (fourCoordinateSignRepresentative F chi))

@[simp] theorem fourCoordinateSignTopMap_apply_coordinate
    (u : G) (i : Fin 4) :
    fourCoordinateSignTopMap F u (fourCoordinateSign F i) =
      fourCoordinateSign F (F.top u i) := by
  apply (fourCoordinateSign_top_eq_iff F u _ _).2
  exact fourCoordinateSignRepresentative_spec F (fourCoordinateSign F i)

@[simp] theorem fourCoordinateSignTopMap_one
    (chi : FourCoordinateSign F) :
    fourCoordinateSignTopMap F 1 chi = chi := by
  obtain ⟨i, rfl⟩ := fourCoordinateSign_surjective F chi
  simp only [fourCoordinateSignTopMap_apply_coordinate, map_one,
    Equiv.Perm.one_apply]

theorem fourCoordinateSignTopMap_mul
    (u v : G) (chi : FourCoordinateSign F) :
    fourCoordinateSignTopMap F (u * v) chi =
      fourCoordinateSignTopMap F u (fourCoordinateSignTopMap F v chi) := by
  obtain ⟨i, rfl⟩ := fourCoordinateSign_surjective F chi
  simp only [fourCoordinateSignTopMap_apply_coordinate, map_mul,
    Equiv.Perm.mul_apply]

/-- The actual pair action on its two realized sign classes. -/
noncomputable def fourCoordinateSignTopPerm
    (u : G) : Equiv.Perm (FourCoordinateSign F) where
  toFun := fourCoordinateSignTopMap F u
  invFun := fourCoordinateSignTopMap F u⁻¹
  left_inv chi := by
    rw [← fourCoordinateSignTopMap_mul]
    simp
  right_inv chi := by
    rw [← fourCoordinateSignTopMap_mul]
    simp

@[simp] theorem fourCoordinateSignTopPerm_apply
    (u : G) (chi : FourCoordinateSign F) :
    fourCoordinateSignTopPerm F u chi = fourCoordinateSignTopMap F u chi :=
  rfl

/-- The induced sign-class action is a homomorphism. -/
noncomputable def fourCoordinateSignTopHom :
    G →* Equiv.Perm (FourCoordinateSign F) where
  toFun := fourCoordinateSignTopPerm F
  map_one' := by
    apply Equiv.ext
    intro chi
    exact fourCoordinateSignTopMap_one F chi
  map_mul' u v := by
    apply Equiv.ext
    intro chi
    exact fourCoordinateSignTopMap_mul F u v chi

@[simp] theorem fourCoordinateSignTopHom_apply_coordinate
    (u : G) (i : Fin 4) :
    fourCoordinateSignTopHom F u (fourCoordinateSign F i) =
      fourCoordinateSign F (F.top u i) :=
  fourCoordinateSignTopMap_apply_coordinate F u i

/-- The sign action depends only on the literal four-point top
permutation. -/
theorem top_ker_le_fourCoordinateSignTopHom_ker :
    F.top.ker ≤ (fourCoordinateSignTopHom F).ker := by
  intro u hu
  apply MonoidHom.mem_ker.mpr
  apply Equiv.ext
  intro chi
  obtain ⟨i, rfl⟩ := fourCoordinateSign_surjective F chi
  rw [fourCoordinateSignTopHom_apply_coordinate]
  have htop : F.top u = 1 := MonoidHom.mem_ker.mp hu
  rw [htop]
  rfl

/-- Descend the sign action from the original pair action to its faithful
four-point top range. -/
noncomputable def fourCoordinateSignRangeHom :
    F.top.range →* Equiv.Perm (FourCoordinateSign F) :=
  F.top.rangeRestrict.liftOfSurjective F.top.rangeRestrict_surjective
    ⟨fourCoordinateSignTopHom F, by
      intro u hu
      apply top_ker_le_fourCoordinateSignTopHom_ker F
      apply MonoidHom.mem_ker.mpr
      simpa using congrArg Subtype.val (MonoidHom.mem_ker.mp hu)⟩

@[simp] theorem fourCoordinateSignRangeHom_apply
    (u : G) :
    fourCoordinateSignRangeHom F (F.top.rangeRestrict u) =
      fourCoordinateSignTopHom F u :=
  MonoidHom.liftOfRightInverse_comp_apply F.top.rangeRestrict
    (Function.surjInv F.top.rangeRestrict_surjective)
    (Function.rightInverse_surjInv F.top.rangeRestrict_surjective) _ u

/-- Relabel the two literal sign classes by `Fin 2`. -/
noncomputable def twoSignBlockMap
    (htwo : Nat.card (FourCoordinateSign F) = 2) : Fin 4 → Fin 2 :=
  fun i => Finite.equivFinOfCardEq htwo (fourCoordinateSign F i)

/-- The descended action on the two relabelled sign classes. -/
noncomputable def twoSignTopHom
    (htwo : Nat.card (FourCoordinateSign F) = 2) :
    F.top.range →* Equiv.Perm (Fin 2) :=
  (Finite.equivFinOfCardEq htwo).permCongrHom.toMonoidHom.comp
    (fourCoordinateSignRangeHom F)

theorem twoSignBlockMap_equivariant
    (htwo : Nat.card (FourCoordinateSign F) = 2)
    (t : F.top.range) (i : Fin 4) :
    twoSignBlockMap F htwo (t i) =
      twoSignTopHom F htwo t (twoSignBlockMap F htwo i) := by
  obtain ⟨u, rfl⟩ := F.top.rangeRestrict_surjective t
  change Finite.equivFinOfCardEq htwo
      (fourCoordinateSign F (F.top u i)) =
    Finite.equivFinOfCardEq htwo
      (fourCoordinateSignTopHom F u (fourCoordinateSign F i))
  rw [fourCoordinateSignTopHom_apply_coordinate]

attribute [local instance] Fintype.ofFinite

/-- In the two-sign branch every literal sign class has two coordinates. -/
theorem fourCoordinateSign_fibre_card_eq_two
    (htrans : MulAction.IsPretransitive G X)
    (htwo : Nat.card (FourCoordinateSign F) = 2)
    (chi : FourCoordinateSign F) :
    Nat.card {i : Fin 4 // fourCoordinateSign F i = chi} = 2 := by
  let m := Nat.card {i : Fin 4 // fourCoordinateSign F i = chi}
  have hproduct : Nat.card (FourCoordinateSign F) * m = 4 := by
    calc
      Nat.card (FourCoordinateSign F) * m =
          ∑ _psi : FourCoordinateSign F, m := by
        simp only [Finset.sum_const, nsmul_eq_mul, Finset.card_univ,
          Fintype.card_eq_nat_card, Nat.cast_id]
      _ = ∑ psi : FourCoordinateSign F,
          Nat.card {i : Fin 4 // fourCoordinateSign F i = psi} := by
        apply Finset.sum_congr rfl
        intro psi _hpsi
        exact (fourCoordinateSign_fibre_card_eq F htrans psi chi).symm
      _ = Nat.card (Sigma fun psi : FourCoordinateSign F =>
          {i : Fin 4 // fourCoordinateSign F i = psi}) :=
        Nat.card_sigma.symm
      _ = Nat.card (Fin 4) :=
        Nat.card_congr (Equiv.sigmaFiberEquiv (fourCoordinateSign F))
      _ = 4 := Nat.card_fin 4
  rw [htwo] at hproduct
  change m = 2
  omega

/-- Each fibre of the relabelled two-sign block map has two points. -/
theorem twoSignBlockMap_fibre_card
    (htrans : MulAction.IsPretransitive G X)
    (htwo : Nat.card (FourCoordinateSign F) = 2)
    (a : Fin 2) :
    Nat.card {i : Fin 4 // twoSignBlockMap F htwo i = a} = 2 := by
  let e : FourCoordinateSign F ≃ Fin 2 := Finite.equivFinOfCardEq htwo
  calc
    Nat.card {i : Fin 4 // twoSignBlockMap F htwo i = a} =
        Nat.card {i : Fin 4 // fourCoordinateSign F i = e.symm a} := by
      apply Nat.card_congr
      apply Equiv.subtypeEquivRight
      intro i
      change e (fourCoordinateSign F i) = a ↔
        fourCoordinateSign F i = e.symm a
      constructor
      · intro h
        apply e.injective
        simpa using h
      · intro h
        rw [h, e.apply_symm_apply]
    _ = 2 := fourCoordinateSign_fibre_card_eq_two F htrans htwo (e.symm a)

/-- The literal four-point top, equipped with its actual two sign classes,
is itself a binary pair action.  This is the reusable input for the standard
faithful wreath embedding into the degree-four dihedral action. -/
noncomputable def twoSignTopPairFrame
    (htrans : MulAction.IsPretransitive G X)
    (htwo : Nat.card (FourCoordinateSign F) = 2) :
    BinaryPairFrame F.top.range (Fin 2) :=
  binaryPairFrameOfFibreCardTwo F.top.range (twoSignTopHom F htwo)
    (twoSignBlockMap F htwo) (twoSignBlockMap_equivariant F htwo)
    (twoSignBlockMap_fibre_card F htrans htwo)

end BinaryPairFrame

namespace Non2UnipotentPrefixFiniteMenu
namespace PrimitiveAffineImprimitiveBlockTransfer

variable {w : ℕ} {U : PreE7NonPairActionClass w}
  {basePoint : Fin w}
  (block : OriginalMinimalBlock
    (A := preE7NonPairAction w U) basePoint)
  (P : PrimitiveAffineProfile block.Component block.Fibre)
  [Nontrivial block.Fibre]

/-- The specialized literal pair frame witnessing that the actual
four-point top in the two-sign branch preserves two blocks of size two. -/
noncomputable def degreeThreeFourBlockTwoSign_topPairFrame
    (hr : Nat.card block.Fibre = 3)
    (hs : Nat.card block.Points = 4)
    (hcomponent : Nat.card block.Component = 6)
    (htwo : (degreeThreeFourBlockSignedIsotypeProfile
      block P hr hs hcomponent).isotypeCount = 2) :
    let C := degreeThreeFourBlockPairChart block P hr hs hcomponent
    BinaryPairFrame C.frame.top.range (Fin 2) := by
  let C := degreeThreeFourBlockPairChart block P hr hs hcomponent
  have htwo' : Nat.card (BinaryPairFrame.FourCoordinateSign C.frame) = 2 := by
    simpa only [degreeThreeFourBlockSignedIsotypeProfile,
      BinaryPairFrame.fourCoordinateSignedIsotypeProfile,
      DegreeThreeFourBlockSignedIsotypeProfile.isotypeCount, C] using htwo
  exact BinaryPairFrame.twoSignTopPairFrame C.frame C.pretransitive htwo'

end PrimitiveAffineImprimitiveBlockTransfer
end Non2UnipotentPrefixFiniteMenu
end SymmetricSubgroupAsymptotics

end
