import SymmetricSubgroupAsymptotics.ScalarFourCentralC4KilledCubic
import Mathlib.Algebra.Group.TypeTags.Finite
import Mathlib.Data.ZMod.Basic

/-! The killed cyclic-top branch is a quotient of the original central
cyclic-four kernel, retaining its original bound c. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.ScalarFourCentralC4TopCoordinates
variable {Q T H : Type} [Group Q] [Group T] [Group H] {c d : ℕ}
  (D : ScalarFourCentralC4TopCoordinates Q T c d)

/-- Killing a generator of the actual cyclic top leaves only original
kernel images. This is an equality of images for the same quotient map. -/
theorem killed_top_kernel_covers (f : Q →* H) (n : Q)
    (hn : D.top n=D.cubic) (hfn : f n=1)
    (hcyclic : Subgroup.zpowers D.cubic=⊤) (g : Q) :
    ∃ k : D.top.ker, f (k : Q)=f g := by
  have hg : D.top g ∈ Subgroup.zpowers D.cubic := by rw [hcyclic]; trivial
  obtain ⟨a,ha⟩ := Subgroup.mem_zpowers_iff.mp hg
  refine ⟨⟨g*(n^a)⁻¹,?_⟩,?_⟩
  · change D.top (g*(n^a)⁻¹)=1
    rw [map_mul,map_inv,map_zpow,hn,ha, mul_inv_cancel]
  · change f (g*(n^a)⁻¹)=f g
    rw [map_mul,map_inv,map_zpow,hfn,one_zpow,inv_one,mul_one]

/-- Every element of the actual quotient comes from the original central
kernel when the quotient kills an actual cyclic-top generator. -/
theorem killed_top_central_surjective (f : Q →* H) (hf : Function.Surjective f)
    (n : Q) (hn : D.top n=D.cubic) (hfn : f n=1)
    (hcyclic : Subgroup.zpowers D.cubic=⊤) :
    Function.Surjective (fun z : D.active.ker => f ((z : D.top.ker) : Q)) := by
  intro h
  obtain ⟨g,rfl⟩ := hf h
  obtain ⟨k,hk⟩ := D.killed_top_kernel_covers f n hn hfn hcyclic g
  obtain ⟨z,hz⟩ := D.kernel_image_central f n hn hfn k
  exact ⟨z,hz.trans hk⟩

theorem killed_top_card_le [Finite Q] [Finite H]
    (f : Q →* H) (hf : Function.Surjective f) (n : Q)
    (hn : D.top n=D.cubic) (hfn : f n=1)
    (hcyclic : Subgroup.zpowers D.cubic=⊤) : Nat.card H≤4^c := by
  calc
    Nat.card H ≤ Nat.card D.active.ker :=
      Nat.card_le_card_of_surjective _ (D.killed_top_central_surjective f hf n hn hfn hcyclic)
    _ ≤ Nat.card (Fin c → Multiplicative (ZMod 4)) :=
      Nat.card_le_card_of_injective _ D.centralCoordinates_injective
    _ = 4^c := by
      rw [Nat.card_fun,Nat.card_congr Multiplicative.toAdd]
      simp

end SymmetricSubgroupAsymptotics.ScalarFourCentralC4TopCoordinates
