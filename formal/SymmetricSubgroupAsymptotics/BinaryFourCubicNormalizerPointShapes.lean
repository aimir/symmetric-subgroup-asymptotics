import SymmetricSubgroupAsymptotics.BinaryFourSymmetricEnvelopeAction
import SymmetricSubgroupAsymptotics.BinaryCoinducedNormalizerPointCover

/-! Tiny normalized physical-point covers for the outer zero-four joint
bound. These are sixteen-point coordinate identities; no group or normal
subgroup census and no final head estimate is a premise. -/
set_option autoImplicit false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics.BinaryFourCubicNormalizerPointShapes
open BinaryFourBlockAugmentation

abbrev Points := Local × Fin 4

def blockCycle : Equiv.Perm (Fin 4) := Equiv.swap 1 2 * Equiv.swap 1 3

def rotate (x : Points) : Points :=
  if x.2 = 0 then (localCycle x.1,0) else (x.1,blockCycle x.2)

def rotation : Equiv.Perm Points where
  toFun := rotate
  invFun x := rotate (rotate x)
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def translate (v : Local) (x : Points) : Points :=
  if x.2 = 0 then x else (x.1+v,x.2)

def translation (v : Local) : Equiv.Perm Points where
  toFun := translate v
  invFun := translate v
  left_inv := by revert v; decide +kernel
  right_inv := by revert v; decide +kernel

def reflect (x : Points) : Points :=
  (fun i => x.1 (Equiv.swap 0 1 i),Equiv.swap 2 3 x.2)

def reflection : Equiv.Perm Points where
  toFun := reflect
  invFun := reflect
  left_inv := by decide +kernel
  right_inv := by decide +kernel

theorem rotation_cube : rotation^3 = 1 := by decide +kernel

theorem translation_commutes (v : Local) : rotation * translation v = translation v * rotation := by
  revert v
  decide +kernel

theorem reflection_inverts : reflection * rotation * reflection⁻¹ = rotation⁻¹ := by
  decide +kernel

def complementVector (v : Local) : Local :=
  if v = ![1,0] then ![0,1] else ![1,0]

def translationRepresentatives (v : Local) : Fin 3 → Points :=
  ![(![1,0],0),(0,1),(complementVector v,1)]

theorem translation_cover (v : Local) (hv : v ≠ 0) (x : Points) :
    rotation x = x ∨ ∃ j : Fin 3, ∃ n : Fin 3, ∃ m : Fin 2,
      (rotation^n.val * (translation v)^m.val) (translationRepresentatives v j) = x := by
  revert v hv x
  decide +kernel

def reflectionRepresentatives : Fin 4 → Points :=
  ![(![1,0],0),(0,1),(![1,1],1),(![1,0],1)]

theorem reflection_cover (x : Points) :
    rotation x = x ∨ ∃ j : Fin 4, ∃ n : Fin 3, ∃ m : Fin 2,
      (rotation^n.val * reflection^m.val) (reflectionRepresentatives j) = x := by
  revert x
  decide +kernel

end SymmetricSubgroupAsymptotics.BinaryFourCubicNormalizerPointShapes
end
