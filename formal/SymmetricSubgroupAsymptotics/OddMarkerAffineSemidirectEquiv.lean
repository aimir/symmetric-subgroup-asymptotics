import SymmetricSubgroupAsymptotics.OddMarkerAffineCoordinateLaws
import Mathlib.GroupTheory.SemidirectProduct
import Mathlib.LinearAlgebra.Pi

/-! The actual natural S3 is its ternary-translation/binary-sign
semidirect product. The six local coordinate laws were proved separately;
this group equivalence and its cardinal argument are structural. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.OddMarkerAffineSemidirectEquiv
open OddMarkerTernaryChart OddMarkerAffineCoordinateLaws

abbrev C3 := Multiplicative (ZMod 3)
abbrev C2 := Multiplicative (ZMod 2)

def scalarAction : C2 →* MulAut C3 where
  toFun s := (LinearEquiv.smulOfUnit (signUnitHom s) :
    ZMod 3 ≃ₗ[ZMod 3] ZMod 3).toAddEquiv.toMultiplicative
  map_one' := by
    apply MulEquiv.ext
    intro z
    apply Multiplicative.toAdd.injective
    change signScalar 1*z.toAdd=z.toAdd
    rw [signScalar_one,one_mul]
  map_mul' s t := by
    apply MulEquiv.ext
    intro z
    apply Multiplicative.toAdd.injective
    change signScalar (s*t)*z.toAdd=signScalar s*(signScalar t*z.toAdd)
    rw [signScalar_mul,mul_assoc]

abbrev Model := C3 ⋊[scalarAction] C2

instance : Finite Model := Finite.of_equiv (C3 × C2) SemidirectProduct.equivProd.symm

def hom : OddMarkerGroup →* Model where
  toFun g := ⟨Multiplicative.ofAdd (offset g),oddMarkerSign g⟩
  map_one' := by
    apply SemidirectProduct.ext
    · exact congrArg Multiplicative.ofAdd offset_one
    · exact map_one oddMarkerSign
  map_mul' g h := by
    apply SemidirectProduct.ext
    · exact congrArg Multiplicative.ofAdd (offset_mul g h)
    · exact map_mul oddMarkerSign g h

theorem hom_injective : Function.Injective hom := by
  intro g h he
  apply coordinates_injective
  apply Prod.ext
  · exact congrArg (fun z : Model => z.left.toAdd) he
  · exact congrArg (fun z : Model => z.right) he

def equiv : OddMarkerGroup ≃* Model := by
  have hthree : Nat.card C3=3 :=
    (Nat.card_congr (Multiplicative.toAdd : C3 ≃ ZMod 3)).trans (Nat.card_zmod 3)
  have htwo : Nat.card C2=2 :=
    (Nat.card_congr (Multiplicative.toAdd : C2 ≃ ZMod 2)).trans (Nat.card_zmod 2)
  have hmodel : Nat.card Model=6 := by
    rw [Nat.card_congr (SemidirectProduct.equivProd : Model ≃ C3 × C2),
      Nat.card_prod,hthree,htwo]
  exact MulEquiv.ofBijective hom ((Nat.bijective_iff_injective_and_card hom).mpr
    ⟨hom_injective,oddMarker_group_card.trans hmodel.symm⟩)

end SymmetricSubgroupAsymptotics.OddMarkerAffineSemidirectEquiv
