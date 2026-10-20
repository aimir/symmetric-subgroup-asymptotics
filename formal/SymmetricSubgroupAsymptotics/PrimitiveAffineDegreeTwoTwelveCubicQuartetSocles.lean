import SymmetricSubgroupAsymptotics.BinaryThreeQuartetCubicImageSocles
import SymmetricSubgroupAsymptotics.FiniteNormalRegistrySocleOfQuotientBounds
import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoTwelvePairFiniteCatalogueRows1To50
import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoTwelvePairFiniteCatalogueRows51To100

/-! Six unchanged original actions share one correlated binary/cubic
model. Gauged literal quartet charts retain every affine offset and all
original normal quotients. No normal-state census or order match is used. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoTwelveCubicQuartetSocles
open BinaryThreeQuartetCubicImageSocles
open Non2UnipotentPrefixFiniteMenu.PrimitiveAffineImprimitiveBlockTransfer
open DegreeTwoTwelvePairFiniteCatalogue

def row6PointChart : Plane × CyclicThree ≃ Fin 12 where
  toFun x := (![0, 3, 6, 9, 2, 8, 11, 5, 1, 4, 10, 7] : Fin 12 → Fin 12)
    ⟨4*(Multiplicative.toAdd x.2).val + (BinaryThreeQuartetLiteralSocles.planeLabel x.1).val,
      by have h := ZMod.val_lt (Multiplicative.toAdd x.2); have h' := (BinaryThreeQuartetLiteralSocles.planeLabel x.1).isLt; omega⟩
  invFun x := (BinaryThreeQuartetLiteralSocles.planeLabel.symm (![0, 0, 0, 1, 1, 3, 2, 3, 1, 3, 2, 2] x),
    Multiplicative.ofAdd (![0, 2, 1, 0, 2, 1, 0, 2, 1, 0, 2, 1] x))
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def row6Lifts : Fin 3 → Model :=
  ![⟨Multiplicative.ofAdd (fun x => ![![1, 1, 0], ![0, 0, 0]] x.1 (⟨(Multiplicative.toAdd x.2).val,ZMod.val_lt _⟩ : Fin 3)), Multiplicative.ofAdd 1⟩, ⟨Multiplicative.ofAdd (fun x => ![![1, 1, 0], ![1, 0, 1]] x.1 (⟨(Multiplicative.toAdd x.2).val,ZMod.val_lt _⟩ : Fin 3)), Multiplicative.ofAdd 2⟩, ⟨Multiplicative.ofAdd (fun x => ![![0, 0, 0], ![1, 1, 1]] x.1 (⟨(Multiplicative.toAdd x.2).val,ZMod.val_lt _⟩ : Fin 3)), Multiplicative.ofAdd 0⟩]

theorem row6_bindings (i : Fin 3) : literalAction row6PointChart (row6Lifts i) = row6Generators i := by
  apply Equiv.ext
  intro x
  revert i x
  decide +kernel

theorem row6AtTwo_quotientSocle (N : Subgroup Row6Top) [N.Normal] :
    SocleNormalGeneratorBound (Row6Top ⧸ N) 2 :=
  quotientSocle row6PointChart row6Lifts row6Generators row6_bindings 0 rfl N

def row6AtTwo_family : row6Interface.normalRegistry.QuotientSocleGeneratorFamily 2 :=
  .ofQuotientBounds _ (fun N => by letI := N.2; exact row6AtTwo_quotientSocle N.1)

def row7PointChart : Plane × CyclicThree ≃ Fin 12 where
  toFun x := (![0, 5, 6, 11, 3, 10, 9, 4, 1, 8, 7, 2] : Fin 12 → Fin 12)
    ⟨4*(Multiplicative.toAdd x.2).val + (BinaryThreeQuartetLiteralSocles.planeLabel x.1).val,
      by have h := ZMod.val_lt (Multiplicative.toAdd x.2); have h' := (BinaryThreeQuartetLiteralSocles.planeLabel x.1).isLt; omega⟩
  invFun x := (BinaryThreeQuartetLiteralSocles.planeLabel.symm (![0, 0, 3, 0, 3, 1, 2, 2, 1, 2, 1, 3] x),
    Multiplicative.ofAdd (![0, 2, 2, 1, 1, 0, 0, 2, 2, 1, 1, 0] x))
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def row7Lifts : Fin 3 → Model :=
  ![⟨Multiplicative.ofAdd (fun x => ![![0, 0, 0], ![0, 1, 1]] x.1 (⟨(Multiplicative.toAdd x.2).val,ZMod.val_lt _⟩ : Fin 3)), Multiplicative.ofAdd 0⟩, ⟨Multiplicative.ofAdd (fun x => ![![1, 1, 0], ![0, 1, 1]] x.1 (⟨(Multiplicative.toAdd x.2).val,ZMod.val_lt _⟩ : Fin 3)), Multiplicative.ofAdd 1⟩, ⟨Multiplicative.ofAdd (fun x => ![![1, 1, 1], ![1, 1, 1]] x.1 (⟨(Multiplicative.toAdd x.2).val,ZMod.val_lt _⟩ : Fin 3)), Multiplicative.ofAdd 0⟩]

theorem row7_bindings (i : Fin 3) : literalAction row7PointChart (row7Lifts i) = row7Generators i := by
  apply Equiv.ext
  intro x
  revert i x
  decide +kernel

theorem row7AtTwo_quotientSocle (N : Subgroup Row7Top) [N.Normal] :
    SocleNormalGeneratorBound (Row7Top ⧸ N) 2 :=
  quotientSocle row7PointChart row7Lifts row7Generators row7_bindings 1 rfl N

def row7AtTwo_family : row7Interface.normalRegistry.QuotientSocleGeneratorFamily 2 :=
  .ofQuotientBounds _ (fun N => by letI := N.2; exact row7AtTwo_quotientSocle N.1)

def row25PointChart : Plane × CyclicThree ≃ Fin 12 where
  toFun x := (![0, 5, 6, 11, 3, 10, 9, 4, 1, 8, 7, 2] : Fin 12 → Fin 12)
    ⟨4*(Multiplicative.toAdd x.2).val + (BinaryThreeQuartetLiteralSocles.planeLabel x.1).val,
      by have h := ZMod.val_lt (Multiplicative.toAdd x.2); have h' := (BinaryThreeQuartetLiteralSocles.planeLabel x.1).isLt; omega⟩
  invFun x := (BinaryThreeQuartetLiteralSocles.planeLabel.symm (![0, 0, 3, 0, 3, 1, 2, 2, 1, 2, 1, 3] x),
    Multiplicative.ofAdd (![0, 2, 2, 1, 1, 0, 0, 2, 2, 1, 1, 0] x))
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def row25Lifts : Fin 3 → Model :=
  ![⟨Multiplicative.ofAdd (fun x => ![![0, 0, 0], ![1, 0, 0]] x.1 (⟨(Multiplicative.toAdd x.2).val,ZMod.val_lt _⟩ : Fin 3)), Multiplicative.ofAdd 0⟩, ⟨Multiplicative.ofAdd (fun x => ![![1, 1, 0], ![0, 1, 1]] x.1 (⟨(Multiplicative.toAdd x.2).val,ZMod.val_lt _⟩ : Fin 3)), Multiplicative.ofAdd 1⟩, ⟨Multiplicative.ofAdd (fun x => ![![1, 1, 1], ![1, 1, 1]] x.1 (⟨(Multiplicative.toAdd x.2).val,ZMod.val_lt _⟩ : Fin 3)), Multiplicative.ofAdd 0⟩]

theorem row25_bindings (i : Fin 3) : literalAction row25PointChart (row25Lifts i) = row25Generators i := by
  apply Equiv.ext
  intro x
  revert i x
  decide +kernel

theorem row25AtTwo_quotientSocle (N : Subgroup Row25Top) [N.Normal] :
    SocleNormalGeneratorBound (Row25Top ⧸ N) 2 :=
  quotientSocle row25PointChart row25Lifts row25Generators row25_bindings 1 rfl N

def row25AtTwo_family : row25Interface.normalRegistry.QuotientSocleGeneratorFamily 2 :=
  .ofQuotientBounds _ (fun N => by letI := N.2; exact row25AtTwo_quotientSocle N.1)

def row26PointChart : Plane × CyclicThree ≃ Fin 12 where
  toFun x := (![0, 3, 6, 9, 2, 8, 11, 5, 1, 4, 10, 7] : Fin 12 → Fin 12)
    ⟨4*(Multiplicative.toAdd x.2).val + (BinaryThreeQuartetLiteralSocles.planeLabel x.1).val,
      by have h := ZMod.val_lt (Multiplicative.toAdd x.2); have h' := (BinaryThreeQuartetLiteralSocles.planeLabel x.1).isLt; omega⟩
  invFun x := (BinaryThreeQuartetLiteralSocles.planeLabel.symm (![0, 0, 0, 1, 1, 3, 2, 3, 1, 3, 2, 2] x),
    Multiplicative.ofAdd (![0, 2, 1, 0, 2, 1, 0, 2, 1, 0, 2, 1] x))
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def row26Lifts : Fin 4 → Model :=
  ![⟨Multiplicative.ofAdd (fun x => ![![1, 1, 0], ![0, 0, 0]] x.1 (⟨(Multiplicative.toAdd x.2).val,ZMod.val_lt _⟩ : Fin 3)), Multiplicative.ofAdd 1⟩, ⟨Multiplicative.ofAdd (fun x => ![![1, 1, 0], ![1, 0, 1]] x.1 (⟨(Multiplicative.toAdd x.2).val,ZMod.val_lt _⟩ : Fin 3)), Multiplicative.ofAdd 2⟩, ⟨Multiplicative.ofAdd (fun x => ![![0, 0, 0], ![1, 1, 1]] x.1 (⟨(Multiplicative.toAdd x.2).val,ZMod.val_lt _⟩ : Fin 3)), Multiplicative.ofAdd 0⟩, ⟨Multiplicative.ofAdd (fun x => ![![1, 1, 1], ![0, 0, 0]] x.1 (⟨(Multiplicative.toAdd x.2).val,ZMod.val_lt _⟩ : Fin 3)), Multiplicative.ofAdd 0⟩]

theorem row26_bindings (i : Fin 4) : literalAction row26PointChart (row26Lifts i) = row26Generators i := by
  apply Equiv.ext
  intro x
  revert i x
  decide +kernel

theorem row26AtTwo_quotientSocle (N : Subgroup Row26Top) [N.Normal] :
    SocleNormalGeneratorBound (Row26Top ⧸ N) 2 :=
  quotientSocle row26PointChart row26Lifts row26Generators row26_bindings 0 rfl N

def row26AtTwo_family : row26Interface.normalRegistry.QuotientSocleGeneratorFamily 2 :=
  .ofQuotientBounds _ (fun N => by letI := N.2; exact row26AtTwo_quotientSocle N.1)

def row56PointChart : Plane × CyclicThree ≃ Fin 12 where
  toFun x := (![0, 3, 6, 9, 1, 10, 7, 4, 2, 5, 8, 11] : Fin 12 → Fin 12)
    ⟨4*(Multiplicative.toAdd x.2).val + (BinaryThreeQuartetLiteralSocles.planeLabel x.1).val,
      by have h := ZMod.val_lt (Multiplicative.toAdd x.2); have h' := (BinaryThreeQuartetLiteralSocles.planeLabel x.1).isLt; omega⟩
  invFun x := (BinaryThreeQuartetLiteralSocles.planeLabel.symm (![0, 0, 0, 1, 3, 1, 2, 2, 2, 3, 1, 3] x),
    Multiplicative.ofAdd (![0, 1, 2, 0, 1, 2, 0, 1, 2, 0, 1, 2] x))
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def row56Lifts : Fin 3 → Model :=
  ![⟨Multiplicative.ofAdd (fun x => ![![0, 0, 0], ![0, 0, 1]] x.1 (⟨(Multiplicative.toAdd x.2).val,ZMod.val_lt _⟩ : Fin 3)), Multiplicative.ofAdd 0⟩, ⟨Multiplicative.ofAdd (fun x => ![![1, 0, 1], ![1, 0, 1]] x.1 (⟨(Multiplicative.toAdd x.2).val,ZMod.val_lt _⟩ : Fin 3)), Multiplicative.ofAdd 0⟩, ⟨Multiplicative.ofAdd (fun x => ![![0, 1, 1], ![1, 1, 0]] x.1 (⟨(Multiplicative.toAdd x.2).val,ZMod.val_lt _⟩ : Fin 3)), Multiplicative.ofAdd 1⟩]

theorem row56_bindings (i : Fin 3) : literalAction row56PointChart (row56Lifts i) = row56Generators i := by
  apply Equiv.ext
  intro x
  revert i x
  decide +kernel

theorem row56AtTwo_quotientSocle (N : Subgroup Row56Top) [N.Normal] :
    SocleNormalGeneratorBound (Row56Top ⧸ N) 2 :=
  quotientSocle row56PointChart row56Lifts row56Generators row56_bindings 2 rfl N

def row56AtTwo_family : row56Interface.normalRegistry.QuotientSocleGeneratorFamily 2 :=
  .ofQuotientBounds _ (fun N => by letI := N.2; exact row56AtTwo_quotientSocle N.1)

def row90PointChart : Plane × CyclicThree ≃ Fin 12 where
  toFun x := (![0, 3, 6, 9, 1, 10, 7, 4, 2, 5, 8, 11] : Fin 12 → Fin 12)
    ⟨4*(Multiplicative.toAdd x.2).val + (BinaryThreeQuartetLiteralSocles.planeLabel x.1).val,
      by have h := ZMod.val_lt (Multiplicative.toAdd x.2); have h' := (BinaryThreeQuartetLiteralSocles.planeLabel x.1).isLt; omega⟩
  invFun x := (BinaryThreeQuartetLiteralSocles.planeLabel.symm (![0, 0, 0, 1, 3, 1, 2, 2, 2, 3, 1, 3] x),
    Multiplicative.ofAdd (![0, 1, 2, 0, 1, 2, 0, 1, 2, 0, 1, 2] x))
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def row90Lifts : Fin 3 → Model :=
  ![⟨Multiplicative.ofAdd (fun x => ![![0, 0, 1], ![0, 0, 1]] x.1 (⟨(Multiplicative.toAdd x.2).val,ZMod.val_lt _⟩ : Fin 3)), Multiplicative.ofAdd 0⟩, ⟨Multiplicative.ofAdd (fun x => ![![0, 0, 0], ![0, 0, 1]] x.1 (⟨(Multiplicative.toAdd x.2).val,ZMod.val_lt _⟩ : Fin 3)), Multiplicative.ofAdd 0⟩, ⟨Multiplicative.ofAdd (fun x => ![![0, 1, 1], ![1, 1, 0]] x.1 (⟨(Multiplicative.toAdd x.2).val,ZMod.val_lt _⟩ : Fin 3)), Multiplicative.ofAdd 1⟩]

theorem row90_bindings (i : Fin 3) : literalAction row90PointChart (row90Lifts i) = row90Generators i := by
  apply Equiv.ext
  intro x
  revert i x
  decide +kernel

theorem row90AtTwo_quotientSocle (N : Subgroup Row90Top) [N.Normal] :
    SocleNormalGeneratorBound (Row90Top ⧸ N) 2 :=
  quotientSocle row90PointChart row90Lifts row90Generators row90_bindings 2 rfl N

def row90AtTwo_family : row90Interface.normalRegistry.QuotientSocleGeneratorFamily 2 :=
  .ofQuotientBounds _ (fun N => by letI := N.2; exact row90AtTwo_quotientSocle N.1)

end SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoTwelveCubicQuartetSocles
end
