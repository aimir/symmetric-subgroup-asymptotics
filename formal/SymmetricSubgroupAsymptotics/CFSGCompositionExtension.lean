import SymmetricSubgroupAsymptotics.CFSGCompositionLengthCardinality
import SymmetricSubgroupAsymptotics.CFSGSimpleProductCompositionLength

/-! Composition-chain bounds across an actual homomorphism with a
semisimple kernel. Every strict step changes either the literal kernel
intersection or the literal quotient image; neither is replaced by a
specially chosen composition series. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGCompositionExtension
open CFSGCompositionLengthCardinality CFSGSimpleProductCompositionLength
variable {G Q : Type} [Group G] [Group Q] (f : G →* Q)

theorem eq_of_kernel_intersection_and_image {H K : Subgroup G} (hle : H ≤ K)
    (hk : H.subgroupOf f.ker = K.subgroupOf f.ker) (hi : H.map f = K.map f) : H = K := by
  apply le_antisymm hle
  intro x hx
  obtain ⟨y, hy, he⟩ := show f x ∈ H.map f by rw [hi]; exact ⟨x, hx, rfl⟩
  have hz : x * y⁻¹ ∈ f.ker := by simp only [MonoidHom.mem_ker, map_mul, map_inv, he, mul_inv_cancel]
  have hzk : (⟨x * y⁻¹, hz⟩ : f.ker) ∈ K.subgroupOf f.ker := K.mul_mem hx (K.inv_mem (hle hy))
  rw [← hk] at hzk
  change x * y⁻¹ ∈ H at hzk
  simpa only [inv_mul_cancel_right] using H.mul_mem hzk hy

theorem strict_step_dichotomy {H K : Subgroup G} (h : H < K) :
    H.subgroupOf f.ker < K.subgroupOf f.ker ∨ H.map f < K.map f := by
  by_cases hk : H.subgroupOf f.ker = K.subgroupOf f.ker
  · right
    exact lt_of_le_of_ne (Subgroup.map_mono h.le)
      (fun hi => h.ne (eq_of_kernel_intersection_and_image f h.le hk hi))
  · exact Or.inl (lt_of_le_of_ne (Subgroup.subgroupOf_mono _ h.le) hk)

variable {I : Type} [Fintype I] [DecidableEq I]
    (S : I → Type) [∀ i, Group (S i)] [∀ i, IsSimpleGroup (S i)]
    (hn : ∀ i, ¬ IsMulCommutative (S i)) (e : f.ker ≃* ∀ i, S i)

def kernelCoordinates (H : Subgroup G) : Subgroup (∀ i, S i) :=
  (H.subgroupOf f.ker).map e.toMonoidHom

omit [Fintype I] [DecidableEq I] [∀ i, IsSimpleGroup (S i)] in
theorem kernelCoordinates_mono {H K : Subgroup G} (h : H ≤ K) :
    kernelCoordinates f S e H ≤ kernelCoordinates f S e K :=
  Subgroup.map_mono (Subgroup.subgroupOf_mono _ h)

omit [Fintype I] [DecidableEq I] [∀ i, IsSimpleGroup (S i)] in
theorem kernelCoordinates_subnormal (H : Subgroup G) (hH : H.IsSubnormal) :
    (kernelCoordinates f S e H).IsSubnormal :=
  hH.subgroupOf.map e.surjective

include hn in
theorem measure_doubles [Finite Q] {H K : Subgroup G} (hH : H.IsSubnormal)
    (hK : K.IsSubnormal) (h : H < K) :
    2 * (2 ^ (support S (kernelCoordinates f S e H)).card * Nat.card (H.map f)) ≤
      2 ^ (support S (kernelCoordinates f S e K)).card * Nat.card (K.map f) := by
  have hm := Finset.card_le_card (support_mono S (kernelCoordinates_mono f S e h.le))
  have hq := Subgroup.card_le_of_le (Subgroup.map_mono (f := f) h.le)
  rcases strict_step_dichotomy f h with hk | hi
  · have hne : kernelCoordinates f S e H ≠ kernelCoordinates f S e K :=
      fun he => hk.ne (Subgroup.map_injective e.injective he)
    have hc := Finset.card_lt_card (support_strict S hn
      (kernelCoordinates_subnormal f S e H hH) (kernelCoordinates_subnormal f S e K hK)
      (lt_of_le_of_ne (kernelCoordinates_mono f S e h.le) hne))
    have hp : 2 * 2 ^ (support S (kernelCoordinates f S e H)).card ≤
        2 ^ (support S (kernelCoordinates f S e K)).card := by
      simpa only [pow_succ, Nat.mul_comm] using
        Nat.pow_le_pow_right (by decide : 1 ≤ 2) (Nat.succ_le_of_lt hc)
    calc
      _ = (2 * 2 ^ (support S (kernelCoordinates f S e H)).card) * Nat.card (H.map f) := by ring
      _ ≤ _ := Nat.mul_le_mul hp hq
  · have hd := two_mul_card_le_of_lt hi
    have hp := Nat.pow_le_pow_right (by decide : 1 ≤ 2) hm
    calc
      _ = 2 ^ (support S (kernelCoordinates f S e H)).card * (2 * Nat.card (H.map f)) := by ring
      _ ≤ _ := Nat.mul_le_mul hp hd

include f e hn in
theorem two_pow_length_le_kernel_factors_mul_image [Finite Q]
    (s : SubnormalCompositionSeries G) :
    2 ^ s.chain.length ≤ 2 ^ Fintype.card I * Nat.card Q := by
  have hb (j : Fin (s.chain.length + 1)) :
      2 ^ j.val ≤ 2 ^ (support S (kernelCoordinates f S e (s.chain j).val)).card *
        Nat.card ((s.chain j).val.map f) := by
    induction j using Fin.induction with
    | zero =>
      exact Nat.mul_pos (pow_pos (by decide : 0 < 2) _)
        (Nat.card_pos (α := (s.chain 0).val.map f))
    | succ j ih =>
      have hd := measure_doubles f S hn e (s.chain j.castSucc).property
        (s.chain j.succ).property (s.chain.step j).1
      have hi := (Nat.mul_le_mul_left 2 ih).trans hd
      simpa only [Fin.val_succ, Fin.val_castSucc, pow_succ, Nat.mul_comm] using hi
  refine (hb (Fin.last _)).trans (Nat.mul_le_mul ?_ (Subgroup.card_le_card_group _))
  exact Nat.pow_le_pow_right (by decide : 1 ≤ 2) (Finset.card_le_univ _)

include f e hn in
theorem length_le_kernel_factors_add_logb_image [Finite Q]
    (s : SubnormalCompositionSeries G) :
    (s.chain.length : ℝ) ≤ Fintype.card I + Real.logb 2 (Nat.card Q) := by
  have h := two_pow_length_le_kernel_factors_mul_image f S hn e s
  have hr : (2 : ℝ) ^ s.chain.length ≤ (2 : ℝ) ^ Fintype.card I * (Nat.card Q : ℝ) := by
    exact_mod_cast h
  have hh := Real.logb_le_logb_of_le (by norm_num : (1 : ℝ) < 2)
    (pow_pos (by norm_num : (0 : ℝ) < 2) _) hr
  have hc : (Nat.card Q : ℝ) ≠ 0 := by exact_mod_cast (Nat.card_pos (α := Q)).ne'
  rw [Real.logb_mul (pow_ne_zero _ (by norm_num)) hc] at hh
  simpa only [Real.logb_pow, Real.logb_self_eq_one (by norm_num : (1 : ℝ) < 2),
    mul_one] using hh

end SymmetricSubgroupAsymptotics.CFSGCompositionExtension
