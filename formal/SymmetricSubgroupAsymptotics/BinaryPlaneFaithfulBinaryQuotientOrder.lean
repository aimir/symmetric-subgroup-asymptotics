import SymmetricSubgroupAsymptotics.BinaryPlaneFaithfulOriginalOrder
import SymmetricSubgroupAsymptotics.BinaryPlaneFaithfulTopMonolith

/-! A binary quotient of the faithful actual A4/S4 linear image has
order at most two. The genuine regular Klein range supplies the divisor
four in the actual quotient kernel. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.BinaryPlaneFaithfulBinaryQuotientOrder
open BinaryPlaneAlternatingKernelPartition (Frame)
open BinaryPlaneAlternatingCentralizerCommutators (R regular top)

theorem card_le_two (C : Subgroup Frame)
    (hinj : Function.Injective (top C))
    (heven : ∀ p : alternatingGroup (Fin 4), ∃ h : C, (h : Frame).right=p.val)
    (l : R →* C) (ht : ∀ r, top C (l r)=regular r)
    (hlcard : Nat.card l.range=4)
    {B : Type} [Group B] [Finite B] (f : C →* B)
    (hf : Function.Surjective f) (n : ℕ) (hB : Nat.card B=2^n) :
    Nat.card B≤2 := by
  have hc := BinaryPlaneFaithfulOriginalOrder.linear_card C hinj heven
  have hm := f.ker.card_mul_index
  rw [Subgroup.index_ker,MonoidHom.range_eq_top.mpr hf,
    Nat.card_congr Subgroup.topEquiv.toEquiv] at hm
  have hker : f.ker≠⊥ := by
    intro hb
    rw [hb,Subgroup.card_bot,one_mul] at hm
    have hd : 3∣Nat.card B := by
      rw [hm]
      rcases hc with hc | hc <;> rw [hc] <;> norm_num
    rw [hB] at hd
    have hh : 3∣2 := Nat.prime_three.dvd_of_dvd_pow hd
    norm_num at hh
  have hl : l.range≤f.ker :=
    BinaryPlaneFaithfulTopMonolith.range_le_nontrivial_normal C hinj heven
      l ht f.ker inferInstance hker
  have hd : 4∣Nat.card f.ker := by
    simpa only [hlcard] using Subgroup.card_dvd_of_le hl
  have hpow : 2^n≤24 := by
    have hp : 0<Nat.card f.ker := Nat.card_pos
    rw [hB] at hm
    rcases hc with hc | hc <;> nlinarith
  have hn : n≤4 := by
    by_contra h
    have h5 : 5≤n := by omega
    have h32 : 2^5≤2^n := pow_le_pow_right₀ (by omega) h5
    norm_num at h32
    omega
  rw [hB]
  rw [hB] at hm
  obtain ⟨k,hk⟩ := hd
  rcases hc with hc | hc <;> rw [hc] at hm <;>
    interval_cases n <;> norm_num at * <;> omega

end SymmetricSubgroupAsymptotics.BinaryPlaneFaithfulBinaryQuotientOrder
