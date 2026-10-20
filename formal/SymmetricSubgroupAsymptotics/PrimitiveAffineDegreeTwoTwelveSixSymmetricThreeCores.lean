import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoTwelveBinaryTowerGeometry
import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoTwelvePairFiniteCatalogueRows1To50
import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoTwelvePairFiniteCatalogueRows101To150

/-!
# Literal pair towers for the six remaining S₃-core twelve-point tops

Rows 48 and 136--140 preserve the displayed twelve-to-six-to-three pair
towers. Only their original generator point images are checked. Six words
in a retained cycle and transposition cover S₃. The generic tower theorem
then gives a binary kernel, cubic semiregularity, and the relative anchor
on every original normal quotient, without enumerating any of these tops.
-/

set_option autoImplicit false
noncomputable section

namespace SymmetricSubgroupAsymptotics
namespace Non2UnipotentPrefixFiniteMenu
namespace PrimitiveAffineImprimitiveBlockTransfer
namespace DegreeTwoTwelveSixSymmetricThreeCores

open DegreeTwoTwelvePairFiniteCatalogue
open DegreeTwoTwelveBinaryTowerGeometry
open DegreeTwoTwelveSymmetricThreeGeometry
open DegreeTwoTwelveExceptionalOriginalQuotients

private def standardFrame (n : ℕ) : Fin n × ZMod 2 ≃ Fin (n * 2) :=
  (Equiv.prodCongr (Equiv.refl (Fin n))
    (ZMod.finEquiv 2).symm.toEquiv).trans finProdFinEquiv

private def relabelA : Equiv.Perm (Fin 12) where
  toFun := ![0, 5, 6, 11, 1, 8, 2, 7, 3, 10, 4, 9]
  invFun := ![0, 4, 6, 8, 10, 1, 2, 7, 5, 11, 9, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def relabelB : Equiv.Perm (Fin 12) where
  toFun := ![0, 11, 5, 6, 1, 2, 7, 8, 3, 4, 9, 10]
  invFun := ![0, 4, 5, 8, 9, 2, 3, 6, 7, 10, 11, 1]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def relabelC : Equiv.Perm (Fin 12) where
  toFun := ![0, 11, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10]
  invFun := ![0, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 1]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def relabelD : Equiv.Perm (Fin 12) where
  toFun := ![0, 3, 6, 9, 1, 10, 4, 7, 2, 5, 8, 11]
  invFun := ![0, 4, 8, 1, 6, 9, 2, 7, 10, 3, 5, 11]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def frameA : Fin 6 × ZMod 2 ≃ Fin 12 := (standardFrame 6).trans relabelA
def frameB : Fin 6 × ZMod 2 ≃ Fin 12 := (standardFrame 6).trans relabelB
def frameC : Fin 6 × ZMod 2 ≃ Fin 12 := (standardFrame 6).trans relabelC
def frameD : Fin 6 × ZMod 2 ≃ Fin 12 := (standardFrame 6).trans relabelD
def secondFrame : Fin 3 × ZMod 2 ≃ Fin 6 := standardFrame 3

private def cycle : Equiv.Perm (Fin 3) where
  toFun := ![1, 2, 0]
  invFun := ![2, 0, 1]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private theorem cycle_swap_cover (reverse : Bool) (i j : Fin 3) (hne : i ≠ j)
    (s : Equiv.Perm (Fin 3)) : ∃ a : Fin 3, ∃ b : Fin 2,
      (if reverse then cycle⁻¹ else cycle) ^ a.val * Equiv.swap i j ^ b.val = s := by
  decide +kernel +revert

namespace Row48

private def rows : Fin 4 → Fin 6 → Fin 6 := ![
  ![1, 0, 2, 3, 4, 5], ![5, 4, 0, 1, 3, 2],
  ![0, 1, 5, 4, 3, 2], ![1, 0, 3, 2, 5, 4]]
private def backs : Fin 4 → Fin 6 → Fin 6 := ![
  ![1, 0, 2, 3, 4, 5], ![2, 3, 5, 4, 1, 0],
  ![0, 1, 5, 4, 3, 2], ![1, 0, 3, 2, 5, 4]]
def tops6 (i : Fin 4) : Equiv.Perm (Fin 6) where
  toFun := rows i
  invFun := backs i
  left_inv := by decide +kernel +revert
  right_inv := by decide +kernel +revert
def tops3 : Fin 4 → Equiv.Perm (Fin 3) := ![1, cycle⁻¹, Equiv.swap 1 2, 1]
theorem first_checked : ∀ i, BinaryPairFrame.Preserves frameA (row48Generators i) (tops6 i) := by
  unfold BinaryPairFrame.Preserves
  decide +kernel
theorem second_checked : ∀ i, BinaryPairFrame.Preserves secondFrame (tops6 i) (tops3 i) := by
  unfold BinaryPairFrame.Preserves
  decide +kernel
def tower : Tower Row48Top :=
  ofGenerators frameA secondFrame row48Generators tops6 tops3 first_checked second_checked
theorem onto : Function.Surjective tower.beta := by
  apply ofGenerators_beta_onto frameA secondFrame row48Generators tops6 tops3
    first_checked second_checked (1 : Fin 4) (2 : Fin 4)
  exact cycle_swap_cover true 1 2 (by decide)
def geometry : TopGeometry row48Interface :=
  Tower.toTopGeometry (D := row48Interface) tower onto
def certificate : RowCertificate row48Interface := geometry.certificate

end Row48

namespace Row136

private def rows : Fin 3 → Fin 6 → Fin 6 := ![
  ![0, 1, 2, 3, 4, 5], ![2, 3, 4, 5, 1, 0], ![5, 4, 3, 2, 1, 0]]
private def backs : Fin 3 → Fin 6 → Fin 6 := ![
  ![0, 1, 2, 3, 4, 5], ![5, 4, 0, 1, 2, 3], ![5, 4, 3, 2, 1, 0]]
def tops6 (i : Fin 3) : Equiv.Perm (Fin 6) where
  toFun := rows i
  invFun := backs i
  left_inv := by decide +kernel +revert
  right_inv := by decide +kernel +revert
def tops3 : Fin 3 → Equiv.Perm (Fin 3) := ![1, cycle, Equiv.swap 0 2]
theorem first_checked : ∀ i, BinaryPairFrame.Preserves frameB (row136Generators i) (tops6 i) := by
  unfold BinaryPairFrame.Preserves
  decide +kernel
theorem second_checked : ∀ i, BinaryPairFrame.Preserves secondFrame (tops6 i) (tops3 i) := by
  unfold BinaryPairFrame.Preserves
  decide +kernel
def tower : Tower Row136Top :=
  ofGenerators frameB secondFrame row136Generators tops6 tops3 first_checked second_checked
theorem onto : Function.Surjective tower.beta := by
  apply ofGenerators_beta_onto frameB secondFrame row136Generators tops6 tops3
    first_checked second_checked (1 : Fin 3) (2 : Fin 3)
  exact cycle_swap_cover false 0 2 (by decide)
def geometry : TopGeometry row136Interface :=
  Tower.toTopGeometry (D := row136Interface) tower onto
def certificate : RowCertificate row136Interface := geometry.certificate

end Row136

namespace Row137

private def rows : Fin 5 → Fin 6 → Fin 6 := ![
  ![0, 1, 2, 3, 4, 5], ![0, 1, 2, 3, 4, 5], ![0, 1, 3, 2, 5, 4],
  ![4, 5, 1, 0, 3, 2], ![0, 1, 5, 4, 3, 2]]
private def backs : Fin 5 → Fin 6 → Fin 6 := ![
  ![0, 1, 2, 3, 4, 5], ![0, 1, 2, 3, 4, 5], ![0, 1, 3, 2, 5, 4],
  ![3, 2, 5, 4, 0, 1], ![0, 1, 5, 4, 3, 2]]
def tops6 (i : Fin 5) : Equiv.Perm (Fin 6) where
  toFun := rows i
  invFun := backs i
  left_inv := by decide +kernel +revert
  right_inv := by decide +kernel +revert
def tops3 : Fin 5 → Equiv.Perm (Fin 3) := ![1, 1, 1, cycle⁻¹, Equiv.swap 1 2]
theorem first_checked : ∀ i, BinaryPairFrame.Preserves frameB (row137Generators i) (tops6 i) := by
  unfold BinaryPairFrame.Preserves
  decide +kernel
theorem second_checked : ∀ i, BinaryPairFrame.Preserves secondFrame (tops6 i) (tops3 i) := by
  unfold BinaryPairFrame.Preserves
  decide +kernel
def tower : Tower Row137Top :=
  ofGenerators frameB secondFrame row137Generators tops6 tops3 first_checked second_checked
theorem onto : Function.Surjective tower.beta := by
  apply ofGenerators_beta_onto frameB secondFrame row137Generators tops6 tops3
    first_checked second_checked (3 : Fin 5) (4 : Fin 5)
  exact cycle_swap_cover true 1 2 (by decide)
def geometry : TopGeometry row137Interface :=
  Tower.toTopGeometry (D := row137Interface) tower onto
def certificate : RowCertificate row137Interface := geometry.certificate

end Row137

namespace Row138

private def rows : Fin 4 → Fin 6 → Fin 6 := ![
  ![0, 1, 2, 3, 4, 5], ![5, 4, 1, 0, 3, 2],
  ![0, 1, 4, 5, 2, 3], ![0, 1, 5, 4, 3, 2]]
private def backs : Fin 4 → Fin 6 → Fin 6 := ![
  ![0, 1, 2, 3, 4, 5], ![3, 2, 5, 4, 1, 0],
  ![0, 1, 4, 5, 2, 3], ![0, 1, 5, 4, 3, 2]]
def tops6 (i : Fin 4) : Equiv.Perm (Fin 6) where
  toFun := rows i
  invFun := backs i
  left_inv := by decide +kernel +revert
  right_inv := by decide +kernel +revert
def tops3 : Fin 4 → Equiv.Perm (Fin 3) := ![1, cycle⁻¹, Equiv.swap 1 2, Equiv.swap 1 2]
theorem first_checked : ∀ i, BinaryPairFrame.Preserves frameC (row138Generators i) (tops6 i) := by
  unfold BinaryPairFrame.Preserves
  decide +kernel
theorem second_checked : ∀ i, BinaryPairFrame.Preserves secondFrame (tops6 i) (tops3 i) := by
  unfold BinaryPairFrame.Preserves
  decide +kernel
def tower : Tower Row138Top :=
  ofGenerators frameC secondFrame row138Generators tops6 tops3 first_checked second_checked
theorem onto : Function.Surjective tower.beta := by
  apply ofGenerators_beta_onto frameC secondFrame row138Generators tops6 tops3
    first_checked second_checked (1 : Fin 4) (2 : Fin 4)
  exact cycle_swap_cover true 1 2 (by decide)
def geometry : TopGeometry row138Interface :=
  Tower.toTopGeometry (D := row138Interface) tower onto
def certificate : RowCertificate row138Interface := geometry.certificate

end Row138

namespace Row139

private def rows : Fin 4 → Fin 6 → Fin 6 := ![
  ![0, 1, 2, 3, 5, 4], ![0, 1, 2, 3, 5, 4],
  ![3, 2, 4, 5, 1, 0], ![3, 2, 1, 0, 4, 5]]
private def backs : Fin 4 → Fin 6 → Fin 6 := ![
  ![0, 1, 2, 3, 5, 4], ![0, 1, 2, 3, 5, 4],
  ![5, 4, 1, 0, 2, 3], ![3, 2, 1, 0, 4, 5]]
def tops6 (i : Fin 4) : Equiv.Perm (Fin 6) where
  toFun := rows i
  invFun := backs i
  left_inv := by decide +kernel +revert
  right_inv := by decide +kernel +revert
def tops3 : Fin 4 → Equiv.Perm (Fin 3) := ![1, 1, cycle, Equiv.swap 0 1]
theorem first_checked : ∀ i, BinaryPairFrame.Preserves frameD (row139Generators i) (tops6 i) := by
  unfold BinaryPairFrame.Preserves
  decide +kernel
theorem second_checked : ∀ i, BinaryPairFrame.Preserves secondFrame (tops6 i) (tops3 i) := by
  unfold BinaryPairFrame.Preserves
  decide +kernel
def tower : Tower Row139Top :=
  ofGenerators frameD secondFrame row139Generators tops6 tops3 first_checked second_checked
theorem onto : Function.Surjective tower.beta := by
  apply ofGenerators_beta_onto frameD secondFrame row139Generators tops6 tops3
    first_checked second_checked (2 : Fin 4) (3 : Fin 4)
  exact cycle_swap_cover false 0 1 (by decide)
def geometry : TopGeometry row139Interface :=
  Tower.toTopGeometry (D := row139Interface) tower onto
def certificate : RowCertificate row139Interface := geometry.certificate

end Row139

namespace Row140

private def rows : Fin 5 → Fin 6 → Fin 6 := ![
  ![0, 1, 2, 3, 4, 5], ![0, 1, 2, 3, 4, 5], ![4, 5, 1, 0, 3, 2],
  ![0, 1, 5, 4, 3, 2], ![0, 1, 4, 5, 2, 3]]
private def backs : Fin 5 → Fin 6 → Fin 6 := ![
  ![0, 1, 2, 3, 4, 5], ![0, 1, 2, 3, 4, 5], ![3, 2, 5, 4, 0, 1],
  ![0, 1, 5, 4, 3, 2], ![0, 1, 4, 5, 2, 3]]
def tops6 (i : Fin 5) : Equiv.Perm (Fin 6) where
  toFun := rows i
  invFun := backs i
  left_inv := by decide +kernel +revert
  right_inv := by decide +kernel +revert
def tops3 : Fin 5 → Equiv.Perm (Fin 3) := ![1, 1, cycle⁻¹, Equiv.swap 1 2, Equiv.swap 1 2]
theorem first_checked : ∀ i, BinaryPairFrame.Preserves frameB (row140Generators i) (tops6 i) := by
  unfold BinaryPairFrame.Preserves
  decide +kernel
theorem second_checked : ∀ i, BinaryPairFrame.Preserves secondFrame (tops6 i) (tops3 i) := by
  unfold BinaryPairFrame.Preserves
  decide +kernel
def tower : Tower Row140Top :=
  ofGenerators frameB secondFrame row140Generators tops6 tops3 first_checked second_checked
theorem onto : Function.Surjective tower.beta := by
  apply ofGenerators_beta_onto frameB secondFrame row140Generators tops6 tops3
    first_checked second_checked (2 : Fin 5) (3 : Fin 5)
  exact cycle_swap_cover true 1 2 (by decide)
def geometry : TopGeometry row140Interface :=
  Tower.toTopGeometry (D := row140Interface) tower onto
def certificate : RowCertificate row140Interface := geometry.certificate

end Row140

end DegreeTwoTwelveSixSymmetricThreeCores
end PrimitiveAffineImprimitiveBlockTransfer
end Non2UnipotentPrefixFiniteMenu
end SymmetricSubgroupAsymptotics

end
