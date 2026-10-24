import SymmetricSubgroupAsymptotics.CFSGSuzukiTorusFirstLayer
import SymmetricSubgroupAsymptotics.CFSGSuzukiCentralPermutationDegree

/-! Exact central extension data of the ACTUAL Suzuki unipotent group.
The square map and the literal torus weight are recorded before applying
any prime-field annihilator or point-stabilizer estimate. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Classical CharTwo
namespace SymmetricSubgroupAsymptotics.CFSGSuzukiCentralExtensionLayers
open CFSGSuzukiFieldParameters CFSGSuzukiUnipotent CFSGSuzukiTorus

def centralHom (m : ℕ) : Multiplicative (Field m) →* unipotentSubgroup m where
  toFun b := coordinateElement m 0 b.toAdd
  map_one' := coordinateElement_zero m
  map_mul' b c := by
    change coordinateElement m 0 (b.toAdd + c.toAdd) =
      coordinateElement m 0 b.toAdd * coordinateElement m 0 c.toAdd
    rw [coordinateElement_mul]
    simp only [map_zero, zero_mul, add_zero]

theorem centralHom_injective (m : ℕ) : Function.Injective (centralHom m) := by
  intro a b he
  exact congrArg (fun g : unipotentSubgroup m =>
    (g.val : CFSG.Models.SuzukiConstruction.Mat m) 2 0) he

theorem centralHom_range (m : ℕ) : (centralHom m).range = (firstParameterHom m).ker := by
  apply le_antisymm
  · rintro g ⟨b, rfl⟩
    change (Multiplicative.ofAdd (0 : Field m)) = 1
    rfl
  · intro g hg
    obtain ⟨a, b, hab⟩ := g.property
    have he : g = coordinateElement m a b := Subtype.ext hab
    have ha : a = 0 := by
      change firstParameter m g = 0 at hg
      rw [he, firstParameter_coordinateElement] at hg
      exact hg
    refine ⟨Multiplicative.ofAdd b, ?_⟩
    change coordinateElement m 0 b = g
    rw [he, ha]

theorem centralHom_mem_center (m : ℕ) (b : Multiplicative (Field m)) :
    centralHom m b ∈ Subgroup.center (unipotentSubgroup m) := by
  apply centralParameters_le_center m
  change firstParameter m (coordinateElement m 0 b.toAdd) = 0
  rfl

theorem coordinate_square (m : ℕ) (a b : Field m) :
    coordinateElement m a b * coordinateElement m a b =
      centralHom m (Multiplicative.ofAdd (theta m a * a)) := by
  change coordinateElement m a b * coordinateElement m a b =
    coordinateElement m 0 (theta m a * a)
  rw [coordinateElement_mul]
  simp only [CharTwo.add_self_eq_zero, zero_add]

def centralWeight (m : ℕ) : (Field m)ˣ →* (Field m)ˣ where
  toFun c := (c * Units.map (theta m).toMonoidHom c)⁻¹
  map_one' := by simp
  map_mul' c d := by
    simp only [map_mul, mul_inv_rev]
    ac_rfl

@[simp] theorem centralWeight_val (m : ℕ) (c : (Field m)ˣ) :
    (centralWeight m c : Field m) = ((c : Field m) * theta m (c : Field m))⁻¹ := by
  change (((c * Units.map (theta m).toMonoidHom c)⁻¹ : (Field m)ˣ) : Field m) = _
  simp only [Units.val_inv_eq_inv_val, Units.val_mul, Units.coe_map]
  rfl

theorem centralWeight_surjective (m : ℕ) : Function.Surjective (centralWeight m) := by
  intro t
  obtain ⟨x, hx⟩ := (thetaProduct_bijective m).surjective ((t : Field m)⁻¹)
  have hx0 : x ≠ 0 := by
    intro he
    rw [he, thetaProduct, map_zero, zero_mul] at hx
    exact (inv_ne_zero (Units.ne_zero t)) hx.symm
  refine ⟨Units.mk0 x hx0, ?_⟩
  apply Units.ext
  rw [centralWeight_val]
  change x * theta m x = (t : Field m)⁻¹ at hx
  change (x * theta m x)⁻¹ = (t : Field m)
  rw [hx, inv_inv]

theorem centralHom_torus (m : ℕ) (c : (Field m)ˣ) (b : Multiplicative (Field m)) :
    torusAutHom m c (centralHom m b) =
      centralHom m (Multiplicative.ofAdd ((centralWeight m c : Field m) * b.toAdd)) := by
  change torusAction m c (coordinateElement m 0 b.toAdd) =
    coordinateElement m 0 ((centralWeight m c : Field m) * b.toAdd)
  rw [torusAction_coordinateElement]
  simp only [mul_zero, centralWeight_val]

end SymmetricSubgroupAsymptotics.CFSGSuzukiCentralExtensionLayers
