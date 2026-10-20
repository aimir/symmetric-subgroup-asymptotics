import SymmetricSubgroupAsymptotics.BinaryPlaneWreathActualOddKernelStructure
import SymmetricSubgroupAsymptotics.PermutationalWreathProduct
import SymmetricSubgroupAsymptotics.BinaryPlaneAlternatingKernelPartition

/-! The retained eight-point comparator is the ACTUAL sign image on eight
points. Its kernel is the original preimage of the odd linear kernel.
The A4/S4 top can be nonbinary; no comparator socle bound is claimed. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped Classical

namespace SymmetricSubgroupAsymptotics.BinaryPlaneAlternatingRetainedComparator
open BinaryPlaneWreathIrreducible BinaryPlaneWreathActualOddKernel
abbrev R := Fin 4
abbrev Q := Equiv.Perm (Fin 4)
abbrev D := Multiplicative (ZMod 2)
abbrev Signs := Sign (R := Q) (I := R)
abbrev BinaryWreath := PermutationalWreathProduct D Q R
local instance : Fintype D := Fintype.ofEquiv (ZMod 2) Multiplicative.ofAdd

private def coordinates : Signs →* BinaryWreath where
  toFun g := ⟨fun i => Multiplicative.ofAdd (g.left.toAdd.1 i),g.right⟩
  map_one' := by
    apply PermutationalWreathProduct.ext
    · funext i; rfl
    · rfl
  map_mul' g h := by
    apply PermutationalWreathProduct.ext
    · funext i
      apply Multiplicative.toAdd.injective
      rfl
    · rfl

private theorem coordinates_injective : Function.Injective coordinates := by
  intro g h he
  apply SemidirectProduct.ext
  · apply Multiplicative.toAdd.injective
    apply Subtype.ext
    funext i
    exact congrArg (fun w : BinaryWreath => (w.left i).toAdd) he
  · exact congrArg PermutationalWreathProduct.right he

private def pointLabel : D × R ≃ Fin 8 :=
  (Fintype.equivFin (D × R)).trans (Equiv.cast (congrArg Fin (by
    rw [Fintype.card_prod,
      Fintype.card_congr (Multiplicative.toAdd : D ≃ ZMod 2),
      ZMod.card,Fintype.card_fin])))

/-- A faithful action of the complete sign wreath on exactly8
points, including all proper correlated sign subgroups by restriction. -/
def pointAction : Signs →* Equiv.Perm (Fin 8) :=
  pointLabel.permCongrHom.toMonoidHom.comp
    ((PermutationalWreathProduct.toPerm (D := D) (Q := Q) (I := R)
      (Lambda := D)).comp coordinates)

theorem pointAction_injective : Function.Injective pointAction :=
  pointLabel.permCongrHom.injective.comp
    (PermutationalWreathProduct.toPerm_injective.comp coordinates_injective)

variable {G : Type} [Group G]
  (C : Subgroup (W (R := Q) (I := R))) (pi : G →* C)

def signMap : G →* Signs := (signProjection C).comp pi
abbrev retained := (signMap C pi).ker

theorem retained_eq_preimage : retained C pi=(oddKernel C).comap pi := rfl

/-- Exact original normal-interval comparator. Original axes containing
this retained subgroup are paid by one complete quotient weight. -/
def quotientAction : (G ⧸ retained C pi) →* Equiv.Perm (Fin 8) :=
  pointAction.comp (QuotientGroup.kerLift (signMap C pi))

theorem quotientAction_injective : Function.Injective (quotientAction C pi) :=
  pointAction_injective.comp (QuotientGroup.kerLift_injective _)

end SymmetricSubgroupAsymptotics.BinaryPlaneAlternatingRetainedComparator
