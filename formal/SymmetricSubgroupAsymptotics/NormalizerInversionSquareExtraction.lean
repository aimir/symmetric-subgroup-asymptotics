import Mathlib.Algebra.Group.Subgroup.Basic

/-! A normalizing torus inverted by a word already in a subgroup enters
that subgroup whenever its parameter group has surjective squaring.
This is a group argument, independent of any matrix model. -/
set_option autoImplicit false
namespace SymmetricSubgroupAsymptotics.NormalizerInversionSquareExtraction
variable {G A : Type*} [Group G] [Group A]

theorem square_mem_of_inverts (S : Subgroup G) (w t : G) (hw : w ∈ S)
    (ht : t ∈ Subgroup.normalizer (S : Set G)) (hinv : w*t*w⁻¹ = t⁻¹) :
    t^2 ∈ S := by
  have hc : t*w*t⁻¹ ∈ S := (Subgroup.mem_normalizer_iff.mp ht w).mp hw
  have hci : w*t⁻¹*w⁻¹ = t := by
    simpa only [mul_inv_rev, inv_inv, mul_assoc] using congrArg Inv.inv hinv
  have he : (t*w*t⁻¹)*w⁻¹ = t^2 := by
    calc
      _ = t*(w*t⁻¹*w⁻¹) := by simp only [mul_assoc]
      _ = t*t := by rw [hci]
      _ = t^2 := (pow_two t).symm
  exact he ▸ S.mul_mem hc (S.inv_mem hw)

theorem range_le_of_surjective_square (S : Subgroup G) (f : A →* G)
    (hsq : Function.Surjective (fun a : A => a^2)) (w : G) (hw : w ∈ S)
    (hn : ∀ a, f a ∈ Subgroup.normalizer (S : Set G))
    (hi : ∀ a, w*f a*w⁻¹ = (f a)⁻¹) : f.range ≤ S := by
  rintro t ⟨a, rfl⟩
  obtain ⟨b, hb⟩ := hsq a
  rw [← hb, map_pow]
  exact square_mem_of_inverts S w (f b) hw (hn b) (hi b)

end SymmetricSubgroupAsymptotics.NormalizerInversionSquareExtraction
