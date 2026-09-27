import Mathlib.GroupTheory.GroupAction.Blocks
import Mathlib.Algebra.Group.Pointwise.Set.Card

/-! Exact orbit numbers for a normal subgroup of the original transitive
acting group. The stabilizer is the actual point stabilizer; no faithful
quotient action or replacement transitive group is used. -/
set_option autoImplicit false
noncomputable section
open scoped Pointwise
namespace SymmetricSubgroupAsymptotics

variable {G X : Type*} [Group G] [MulAction G X]
    (K : Subgroup G) [K.Normal] [MulAction.IsPretransitive G X] (x : X)

/-- Original normal-subgroup orbits are precisely the original translates
of one orbit, as sets of the original points. -/
def normalOrbitClassesEquivBlockOrbit :
    MulAction.orbitRel.Quotient K X ≃ MulAction.orbit G (MulAction.orbit K x) := by
  let f : MulAction.orbitRel.Quotient K X →
      MulAction.orbit G (MulAction.orbit K x) := fun o =>
    ⟨o.orbit, by
      obtain ⟨g,hg⟩ := MulAction.exists_smul_eq G x o.out
      refine ⟨g,?_⟩
      change g • MulAction.orbit K x = o.orbit
      rw [MulAction.smul_orbit_eq_orbit_smul,hg]
      exact (o.orbit_eq_orbit_out Quotient.out_eq').symm⟩
  apply Equiv.ofBijective f
  constructor
  · intro o o' h
    exact MulAction.orbitRel.Quotient.orbit_injective (congrArg Subtype.val h)
  · intro B
    obtain ⟨g,hg⟩ := B.property
    refine ⟨Quotient.mk'' (g • x),?_⟩
    apply Subtype.ext
    change MulAction.orbit K (g • x) = (B : Set X)
    rw [← MulAction.smul_orbit_eq_orbit_smul]
    exact hg

/-- The set stabilizer of an actual normal-subgroup orbit retains both
the original subgroup and the original point stabilizer. -/
theorem stabilizer_normal_orbit_eq :
    MulAction.stabilizer G (MulAction.orbit K x) = K ⊔ MulAction.stabilizer G x := by
  apply le_antisymm
  · intro g hg
    have hgx : g • x ∈ MulAction.orbit K x := by
      have hx : g • x ∈ g • MulAction.orbit K x :=
        Set.smul_mem_smul_set (MulAction.mem_orbit_self x)
      rw [MulAction.mem_stabilizer_iff.mp hg] at hx
      exact hx
    obtain ⟨z,hz⟩ := hgx
    have hp : (z:G)⁻¹ * g ∈ MulAction.stabilizer G x := by
      apply MulAction.mem_stabilizer_iff.mpr
      rw [mul_smul,← hz]
      exact inv_smul_smul (z:G) x
    have hm : (z:G)*((z:G)⁻¹*g) ∈ K ⊔ MulAction.stabilizer G x :=
      Subgroup.mul_mem _
        ((show K ≤ K ⊔ MulAction.stabilizer G x from le_sup_left) z.property)
        ((show MulAction.stabilizer G x ≤ K ⊔ MulAction.stabilizer G x from
          le_sup_right) hp)
    simpa only [mul_inv_cancel_left] using hm
  · apply sup_le
    · intro g hg
      apply MulAction.mem_stabilizer_iff.mpr
      rw [MulAction.smul_orbit_eq_orbit_smul]
      exact MulAction.orbit_eq_iff.mpr ⟨⟨g,hg⟩,rfl⟩
    · exact (MulAction.IsBlock.orbit_of_normal (N := K) x).stabilizer_le
        (MulAction.mem_orbit_self x)

/-- The number of actual K-orbits is the index of K joined with the
actual point stabilizer. This identity does not require faithfulness. -/
theorem normal_orbit_classes_card_eq_index :
    Nat.card (MulAction.orbitRel.Quotient K X) =
      (K ⊔ MulAction.stabilizer G x).index := by
  rw [Nat.card_congr (normalOrbitClassesEquivBlockOrbit K x)]
  change (MulAction.orbit G (MulAction.orbit K x)).ncard = _
  rw [← MulAction.index_stabilizer,stabilizer_normal_orbit_eq]

/-- Every original normal-subgroup orbit has the same cardinality. -/
theorem normal_orbit_card_eq (o : MulAction.orbitRel.Quotient K X) :
    Nat.card o.orbit = Nat.card (MulAction.orbit K x) := by
  obtain ⟨g,hg⟩ := MulAction.exists_smul_eq G x o.out
  rw [o.orbit_eq_orbit_out Quotient.out_eq',← hg,
    ← MulAction.smul_orbit_eq_orbit_smul]
  exact Set.ncard_smul_set g (MulAction.orbit K x)

/-- The exact product identity uses actual orbit classes, not a list of
orbit labels that might repeat. -/
theorem normal_orbit_card_mul_classes :
    Nat.card (MulAction.orbit K x) * Nat.card (MulAction.orbitRel.Quotient K X) =
      Nat.card X := by
  rw [Nat.card_congr (normalOrbitClassesEquivBlockOrbit K x)]
  exact (MulAction.IsBlock.orbit_of_normal (N := K) x).ncard_block_mul_ncard_orbit_eq
    (MulAction.nonempty_orbit x)

/-- An onto original group homomorphism identifies the orbit number
with the index of the image of the original point stabilizer. -/
theorem kernel_orbit_classes_card_eq_image_index {H : Type*} [Group H]
    (f : G →* H) (hf : Function.Surjective f) :
    Nat.card (MulAction.orbitRel.Quotient f.ker X) =
      ((MulAction.stabilizer G x).map f).index := by
  rw [normal_orbit_classes_card_eq_index,Subgroup.index_map,
    f.range_eq_top_of_surjective hf,Subgroup.index_top,mul_one,sup_comm]

end SymmetricSubgroupAsymptotics
