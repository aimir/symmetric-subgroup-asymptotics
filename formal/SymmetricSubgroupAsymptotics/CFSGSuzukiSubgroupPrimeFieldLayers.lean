import SymmetricSubgroupAsymptotics.CFSGSuzukiCentralExtensionLayers
import Mathlib.Algebra.Algebra.ZMod
import Mathlib.Algebra.Module.ZMod

/-! Prime-field layers of an arbitrary ACTUAL subgroup J of Suzuki U.
Only additive/F2 linearity is used. The square of the very same lift
forces its quadratic first-coordinate value into the same central
intersection; no independent projected stabilizer is introduced. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGSuzukiSubgroupPrimeFieldLayers
open CFSGSuzukiFieldParameters CFSGSuzukiUnipotent CFSGSuzukiCentralExtensionLayers

def centralSubspace (m : ℕ) (J : Subgroup (unipotentSubgroup m)) :
    Submodule (ZMod 2) (Field m) :=
  AddSubgroup.toZModSubmodule 2 (J.comap (centralHom m)).toAddSubgroup'

def vectorSubspace (m : ℕ) (J : Subgroup (unipotentSubgroup m)) :
    Submodule (ZMod 2) (Field m) :=
  AddSubgroup.toZModSubmodule 2 (J.map (firstParameterHom m)).toAddSubgroup'

theorem centralSubspace_ne_top (m : ℕ) (J : Subgroup (unipotentSubgroup m))
    (hJ : ¬(centralHom m).range ≤ J) : centralSubspace m J ≠ ⊤ := by
  intro he
  apply hJ
  rintro u ⟨b, rfl⟩
  change b.toAdd ∈ centralSubspace m J
  rw [he]
  trivial

theorem square_mem_centralSubspace (m : ℕ) (J : Subgroup (unipotentSubgroup m))
    (a : Field m) (ha : a ∈ vectorSubspace m J) :
    theta m a * a ∈ centralSubspace m J := by
  change Multiplicative.ofAdd a ∈ J.map (firstParameterHom m) at ha
  obtain ⟨g, hg, he⟩ := ha
  obtain ⟨x, y, hxy⟩ := g.property
  have hg' : g = coordinateElement m x y := Subtype.ext hxy
  have hx := congrArg (fun z : Multiplicative (Field m) => z.toAdd) he
  change firstParameter m g = a at hx
  rw [hg', firstParameter_coordinateElement] at hx
  have hn : coordinateElement m a y ∈ J := by simpa only [hg', hx] using hg
  change centralHom m (Multiplicative.ofAdd (theta m a * a)) ∈ J
  rw [← coordinate_square m a y]
  exact J.mul_mem hn hn

def centralLayerEquiv (m : ℕ) (J : Subgroup (unipotentSubgroup m)) :
    (J.comap (centralHom m)) ≃ centralSubspace m J where
  toFun z := ⟨z.val.toAdd, z.property⟩
  invFun z := ⟨Multiplicative.ofAdd z.val, z.property⟩
  left_inv _ := rfl
  right_inv _ := rfl

def vectorLayerEquiv (m : ℕ) (J : Subgroup (unipotentSubgroup m)) :
    (J.map (firstParameterHom m)) ≃ vectorSubspace m J where
  toFun z := ⟨z.val.toAdd, z.property⟩
  invFun z := ⟨Multiplicative.ofAdd z.val, z.property⟩
  left_inv _ := rfl
  right_inv _ := rfl

theorem centralSubspace_card (m : ℕ) (J : Subgroup (unipotentSubgroup m)) :
    Nat.card (centralSubspace m J) = Nat.card (J.comap (centralHom m)) :=
  (Nat.card_congr (centralLayerEquiv m J)).symm

theorem vectorSubspace_card (m : ℕ) (J : Subgroup (unipotentSubgroup m)) :
    Nat.card (vectorSubspace m J) = Nat.card (J.map (firstParameterHom m)) :=
  (Nat.card_congr (vectorLayerEquiv m J)).symm

end SymmetricSubgroupAsymptotics.CFSGSuzukiSubgroupPrimeFieldLayers
