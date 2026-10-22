import Mathlib.GroupTheory.Sylow
import Mathlib.Tactic.Group

/-! A homomorphism with central kernel which is injective on one Sylow
separates ALL p-elements. This is stronger than separate injectivity on
opposite p-subgroups, and justifies transporting their intersection. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGCentralKernelPElements
variable {G H : Type*} [Group G] [Group H] {p : ℕ} [Fact p.Prime]

theorem central_p_element_mem (P : Sylow p G) (z : G)
    (hz : z ∈ Subgroup.center G) (hpz : ∃ k : ℕ, z ^ p ^ k = 1) : z ∈ P := by
  obtain ⟨k, hk⟩ := hpz
  obtain ⟨l, _, hl⟩ := (Nat.dvd_prime_pow (Fact.out : p.Prime)).mp
    (orderOf_dvd_of_pow_eq_one hk)
  have hZ : IsPGroup p (Subgroup.zpowers z) :=
    IsPGroup.of_card ((Nat.card_zpowers z).trans hl)
  have hZc : Subgroup.zpowers z ≤ Subgroup.center G := Subgroup.zpowers_le.mpr hz
  have hsup : IsPGroup p (Subgroup.zpowers z ⊔ (P : Subgroup G) : Subgroup G) :=
    hZ.to_sup_of_normal_right' P.isPGroup'
      (hZc.trans (Subgroup.center_le_normalizer _))
  have he := P.is_maximal' hsup le_sup_right
  have hZP : Subgroup.zpowers z ≤ (P : Subgroup G) := by
    rw [← he]
    exact le_sup_left
  exact hZP (Subgroup.mem_zpowers z)

theorem central_kernel_p_element_eq_one (f : G →* H) (P : Sylow p G)
    (hP : Function.Injective (f.comp (P : Subgroup G).subtype))
    (hker : f.ker ≤ Subgroup.center G) (z : G)
    (hz : z ∈ f.ker) (hpz : ∃ k : ℕ, z ^ p ^ k = 1) : z = 1 := by
  have hzP := central_p_element_mem P z (hker hz) hpz
  have he : f.comp (P : Subgroup G).subtype ⟨z, hzP⟩ = f.comp (P : Subgroup G).subtype 1 := by
    change f z = f 1
    rw [map_one]
    exact hz
  exact congrArg Subtype.val (hP he)

theorem eq_of_p_elements (f : G →* H) (P : Sylow p G)
    (hP : Function.Injective (f.comp (P : Subgroup G).subtype))
    (hker : f.ker ≤ Subgroup.center G) (x y : G)
    (hx : ∃ k : ℕ, x ^ p ^ k = 1) (hy : ∃ k : ℕ, y ^ p ^ k = 1)
    (he : f x = f y) : x = y := by
  let z := x * y⁻¹
  have hz : z ∈ f.ker := by change f (x * y⁻¹) = 1; rw [map_mul, map_inv, he, mul_inv_cancel]
  have hxy : Commute x y := by
    have hc := Subgroup.mem_center_iff.mp (hker hz) y
    have hh := congrArg (fun a : G => a * y) hc
    change (y * (x * y⁻¹)) * y = ((x * y⁻¹) * y) * y at hh
    simpa only [mul_assoc, inv_mul_cancel, mul_one] using hh.symm
  obtain ⟨a, ha⟩ := hx
  obtain ⟨b, hb⟩ := hy
  have hxa : x ^ p ^ (a + b) = 1 := by rw [pow_add, pow_mul, ha, one_pow]
  have hyb : y ^ p ^ (a + b) = 1 := by rw [Nat.add_comm a b, pow_add, pow_mul, hb, one_pow]
  have hpz : z ^ p ^ (a + b) = 1 := by
    dsimp only [z]
    rw [hxy.inv_right.mul_pow, hxa, inv_pow, hyb, inv_one, mul_one]
  have hz1 := central_kernel_p_element_eq_one f P hP hker z hz ⟨a + b, hpz⟩
  exact mul_inv_eq_one.mp hz1

theorem disjoint_map (f : G →* H) (P : Sylow p G)
    (hP : Function.Injective (f.comp (P : Subgroup G).subtype))
    (hker : f.ker ≤ Subgroup.center G)
    (U V : Subgroup G) (hU : IsPGroup p U) (hV : IsPGroup p V)
    (hUV : U ⊓ V = ⊥) : U.map f ⊓ V.map f = ⊥ := by
  apply le_antisymm _ bot_le
  rintro g ⟨⟨u, hu, rfl⟩, v, hv, he⟩
  obtain ⟨a, ha⟩ := hU ⟨u, hu⟩
  obtain ⟨b, hb⟩ := hV ⟨v, hv⟩
  have huv : u = v := eq_of_p_elements f P hP hker u v
    ⟨a, congrArg Subtype.val ha⟩ ⟨b, congrArg Subtype.val hb⟩ he.symm
  have hu1 : u = 1 := by
    have hm : u ∈ U ⊓ V := ⟨hu, huv.symm ▸ hv⟩
    simpa only [hUV, Subgroup.mem_bot] using hm
  simp only [hu1, map_one, Subgroup.mem_bot]

end SymmetricSubgroupAsymptotics.CFSGCentralKernelPElements
