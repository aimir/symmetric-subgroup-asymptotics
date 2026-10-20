import SymmetricSubgroupAsymptotics.MarkedC4QuotientProfiles
import Mathlib.GroupTheory.PGroup

/-! Binary normal images in a nonbinary quotient retain no cubic
factor in their actual preimage. This applies to the literal A4/S4
normal menus without choosing replacement denominators. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.SingleCubicNormalBinaryImage
local instance : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩

theorem preimage_le {G Q : Type} [Group G] [Finite G] [Group Q] [Finite Q]
    (f : G →* Q) (hf : Function.Surjective f) (k : ℕ)
    (hG : Nat.card G=3*2^k) (hQ : 3∣Nat.card Q)
    (V : Subgroup G)
    (hmenu : ∀ M : Subgroup G, M.Normal → M≤V ∨ 3∣Nat.card M)
    (L : Subgroup Q) (hL : L.Normal) (hb : IsPGroup 2 L) : L.comap f≤V := by
  have hp := f.ker.card_mul_index
  rw [Subgroup.index_ker,MonoidHom.range_eq_top.mpr hf,
    Nat.card_congr Subgroup.topEquiv.toEquiv] at hp
  obtain ⟨u,hu⟩ := hQ
  have hc : Nat.card f.ker*u=2^k := by
    apply Nat.eq_of_mul_eq_mul_left (by decide : 0<3)
    calc
      3*(Nat.card f.ker*u)=Nat.card f.ker*Nat.card Q := by rw [hu]; ac_rfl
      _=3*2^k := hp.trans hG
  have hnk : ¬3∣Nat.card f.ker := by
    intro hd
    have hh : 3∣2^k := by rw [← hc]; exact dvd_mul_of_dvd_left hd u
    have hh' : 3∣2 := Nat.prime_three.dvd_of_dvd_pow hh
    norm_num at hh'
  obtain ⟨n,hn⟩ := IsPGroup.iff_card.mp hb
  have hcard : Nat.card (L.comap f)=Nat.card f.ker*2^n := by
    rw [MarkedC4.card_comap_of_le_range f L (by rw [MonoidHom.range_eq_top.mpr hf]; exact le_top),hn]
  have hnm : ¬3∣Nat.card (L.comap f) := by
    rw [hcard]
    intro hd
    rcases Nat.prime_three.dvd_mul.mp hd with hd | hd
    · exact hnk hd
    · have hh : 3∣2 := Nat.prime_three.dvd_of_dvd_pow hd
      norm_num at hh
  letI : L.Normal := hL
  rcases hmenu (L.comap f) inferInstance with hm | hm
  · exact hm
  · exact (hnm hm).elim

end SymmetricSubgroupAsymptotics.SingleCubicNormalBinaryImage
