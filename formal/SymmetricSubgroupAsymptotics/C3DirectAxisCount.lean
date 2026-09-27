import SymmetricSubgroupAsymptotics.C3LocalAxisPartition

/-!
# The full-axis regular C3 branch is a direct product

If the first Goursat axis is full, the complete local subgroup is determined
injectively by its entire complementary image.  This gives the source count
needed for the direct-product forward row, while preserving an arbitrary
survival predicate on the original subgroup.
-/

set_option autoImplicit false
noncomputable section
open scoped Classical

namespace SymmetricSubgroupAsymptotics

variable {Z : Type*}

/-- A full first axis forces literal equality with the product of the whole
regular action and the original complementary image. -/
theorem c3_eq_product_of_axis_top
    (H : Subgroup (ternaryRegularAction × Equiv.Perm Z))
    (haxis : H.goursatFst = ⊤) :
    H = (⊤ : Subgroup ternaryRegularAction).prod
      (H.map (MonoidHom.snd ternaryRegularAction (Equiv.Perm Z))) := by
  ext x
  rw [Subgroup.mem_prod]
  constructor
  · intro hx
    exact ⟨Subgroup.mem_top _,⟨x,hx,rfl⟩⟩
  · rintro ⟨_,hx⟩
    obtain ⟨y,hy,he⟩ := hx
    have hu : x.1 * y.1⁻¹ ∈ H.goursatFst := by
      rw [haxis]
      exact Subgroup.mem_top _
    have hpure : (x.1 * y.1⁻¹,1) ∈ H :=
      (Subgroup.mem_goursatFst).mp hu
    have hm := H.mul_mem hpure hy
    have hxy : (x.1 * y.1⁻¹,1) * y = x := by
      apply Prod.ext
      · simp
      · exact he
    simpa only [hxy] using hm

def c3DirectAxisComplement
    (P : Subgroup (ternaryRegularAction × Equiv.Perm Z) → Prop) :
    C3DirectAxisLocalFamily P → Subgroup (Equiv.Perm Z) :=
  fun H => H.1.1.map (MonoidHom.snd ternaryRegularAction (Equiv.Perm Z))

theorem c3DirectAxisComplement_injective
    (P : Subgroup (ternaryRegularAction × Equiv.Perm Z) → Prop) :
    Function.Injective (c3DirectAxisComplement P) := by
  intro H K h
  change H.1.1.map (MonoidHom.snd ternaryRegularAction (Equiv.Perm Z)) =
    K.1.1.map (MonoidHom.snd ternaryRegularAction (Equiv.Perm Z)) at h
  apply Subtype.ext
  apply Subtype.ext
  rw [c3_eq_product_of_axis_top H.1.1 H.2,
    c3_eq_product_of_axis_top K.1.1 K.2,h]

/-- The full-axis branch has at most one local subgroup per complete
complementary subgroup. -/
theorem c3DirectAxis_card_le_subgroupCount (b : ℕ)
    (P : Subgroup (ternaryRegularAction × Equiv.Perm (Fin b)) → Prop) :
    Nat.card (C3DirectAxisLocalFamily P) ≤ subgroupCount b := by
  unfold subgroupCount
  exact Nat.card_le_card_of_injective (c3DirectAxisComplement P)
    (c3DirectAxisComplement_injective P)

end SymmetricSubgroupAsymptotics

end
