import Mathlib.GroupTheory.GroupAction.Basic
import Mathlib.Algebra.Group.Subgroup.Basic
import Mathlib.Data.Finite.Card

/-! Normalizer geometry on the original action. A normalizing element
carries an actual subgroup orbit bijectively onto the orbit of its image
point. Distinct orbit cardinalities therefore force setwise block
preservation. Unique common fixed points are fixed by the normalizer. -/
set_option autoImplicit false
noncomputable section

namespace SymmetricSubgroupAsymptotics.CFSGNormalizerOrbitGeometry

variable {G X : Type*} [Group G] [MulAction G X] (P : Subgroup G)

theorem smul_mem_orbit (g : G) (hg : g ∈ Subgroup.normalizer (P : Set G))
    {x y : X} (hy : y ∈ MulAction.orbit P x) :
    g • y ∈ MulAction.orbit P (g • x) := by
  obtain ⟨p, hp⟩ := MulAction.mem_orbit_iff.mp hy
  have hm : g * p * g⁻¹ ∈ P :=
    ((Subgroup.mem_normalizer_iff.mp hg) p).mp p.property
  apply MulAction.mem_orbit_iff.mpr
  refine ⟨⟨g * p * g⁻¹, hm⟩, ?_⟩
  change (g * (p : G) * g⁻¹) • (g • x) = g • y
  simpa only [mul_smul, inv_smul_smul] using congrArg (g • ·) hp

def orbitEquiv (g : G) (hg : g ∈ Subgroup.normalizer (P : Set G)) (x : X) :
    MulAction.orbit P x ≃ MulAction.orbit P (g • x) where
  toFun y := ⟨g • y, smul_mem_orbit P g hg y.property⟩
  invFun y := ⟨g⁻¹ • y, by
    have h := smul_mem_orbit P g⁻¹
      ((Subgroup.normalizer (P : Set G)).inv_mem hg) y.property
    simpa only [inv_smul_smul] using h⟩
  left_inv y := Subtype.ext (inv_smul_smul g (y : X))
  right_inv y := Subtype.ext (smul_inv_smul g (y : X))

theorem orbit_card_eq (g : G) (hg : g ∈ Subgroup.normalizer (P : Set G)) (x : X) :
    Nat.card (MulAction.orbit P x) = Nat.card (MulAction.orbit P (g • x)) :=
  Nat.card_congr (orbitEquiv P g hg x)

theorem smul_mem_same_orbit_of_card_separates
    (hsep : ∀ x y : X, Nat.card (MulAction.orbit P x) =
      Nat.card (MulAction.orbit P y) → y ∈ MulAction.orbit P x)
    (g : G) (hg : g ∈ Subgroup.normalizer (P : Set G)) (x : X) :
    g • x ∈ MulAction.orbit P x := hsep x (g • x) (orbit_card_eq P g hg x)

theorem normalizer_le_stabilizer_of_unique_fixedPoint (x : X)
    (hfix : ∀ p : P, p • x = x)
    (hunique : ∀ y : X, (∀ p : P, p • y = y) → y = x) :
    Subgroup.normalizer (P : Set G) ≤ MulAction.stabilizer G x := by
  intro g hg
  change g • x = x
  apply hunique
  intro p
  have hm : g⁻¹ * p * g ∈ P :=
    ((Subgroup.mem_normalizer_iff''.mp hg) p).mp p.property
  have he := hfix ⟨g⁻¹ * p * g, hm⟩
  change (g⁻¹ * (p : G) * g) • x = x at he
  have hh := congrArg (g • ·) he
  simpa only [mul_smul, smul_inv_smul] using hh

end SymmetricSubgroupAsymptotics.CFSGNormalizerOrbitGeometry
