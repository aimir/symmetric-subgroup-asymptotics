import SymmetricSubgroupAsymptotics.WeakClassicalOrderCubeNumerics

/-! A sharper actual-C component exponent permits a smaller finite
parameter frontier. All seeds are scalar arithmetic; no group or action
is enumerated. -/
set_option autoImplicit false
namespace SymmetricSubgroupAsymptotics.SymplecticSharpOrderCubeNumerics
open QuadraticRankOrderCubeNumerics

def componentExponent (t : ℕ) : ℕ := 2*(t+1)^2+(t+1)+3

def Capacity (q t : ℕ) : Prop :=
  11≤q ∨ (5≤q ∧ 3≤t) ∨ (4≤q ∧ 4≤t) ∨ (3≤q ∧ 5≤t) ∨ 8≤t

private theorem exponent_double (t : ℕ) (ht : 2≤t) :
    componentExponent (t+1) ≤ 2*componentExponent t := by
  unfold componentExponent
  nlinarith

private theorem even_binary (b : ℕ) : (2:ℕ)^(2*b)≤5^b := by
  rw [pow_mul]
  exact Nat.pow_le_pow_left (by decide) b

private theorem seed_eleven : (11:ℕ)^(3*componentExponent 2)≤5^(11^2-1) := by
  change (11:ℕ)^72≤5^120
  calc
    (11:ℕ)^72=(11^3)^24 := by rw [←pow_mul]
    _ ≤ (5^5)^24 := Nat.pow_le_pow_left (by decide : (11:ℕ)^3≤5^5) 24
    _ = 5^120 := by rw [←pow_mul]

private theorem seed_five : (5:ℕ)^(3*componentExponent 3)≤5^(5^3-1) := by
  change (5:ℕ)^117≤5^124
  exact Nat.pow_le_pow_right (by decide) (by decide)

private theorem seed_four : (4:ℕ)^(3*componentExponent 4)≤5^(4^4-1) := by
  change (4:ℕ)^174≤5^255
  exact (Nat.pow_le_pow_left (by decide : (4:ℕ)≤5) 174).trans
    (Nat.pow_le_pow_right (by decide) (by decide))

private theorem seed_three : (3:ℕ)^(3*componentExponent 5)≤5^(3^5-1) := by
  change (3:ℕ)^243≤5^242
  calc
    (3:ℕ)^243≤3^244 := Nat.pow_le_pow_right (by decide) (by decide)
    _ =(3^4)^61 := by rw [←pow_mul]
    _ ≤(5^3)^61 := Nat.pow_le_pow_left (by decide : (3:ℕ)^4≤5^3) 61
    _ =5^183 := by rw [←pow_mul]
    _ ≤5^242 := Nat.pow_le_pow_right (by decide) (by decide)

private theorem seed_two : (2:ℕ)^(3*componentExponent 8)≤5^(2^8-1) := by
  change (2:ℕ)^522≤5^255
  calc
    (2:ℕ)^522=(2^9)^58 := by rw [←pow_mul]
    _ ≤(5^4)^58 := Nat.pow_le_pow_left (by decide : (2:ℕ)^9≤5^4) 58
    _ =5^232 := by rw [←pow_mul]
    _ ≤5^255 := Nat.pow_le_pow_right (by decide) (by decide)

private theorem field_eleven (q t : ℕ) (hq : 11≤q) (ht : 2≤t) :
    q^(3*componentExponent t)≤5^(q^t-1) :=
  rank_tail q (by omega) componentExponent 2 exponent_double
    (field_tail 11 2 24 12 (by decide) (even_binary 12) (by decide) seed_eleven q hq) t ht

private theorem field_five (q t : ℕ) (hq : 5≤q) (ht : 3≤t) :
    q^(3*componentExponent t)≤5^(q^t-1) :=
  rank_tail q (by omega) componentExponent 3 (fun t ht => exponent_double t (by omega))
    (field_tail 5 3 39 20 (by decide)
      ((Nat.pow_le_pow_right (by decide : 0<2) (by decide : 39≤40)).trans (even_binary 20))
      (by decide) seed_five q hq) t ht

private theorem field_four (q t : ℕ) (hq : 4≤q) (ht : 4≤t) :
    q^(3*componentExponent t)≤5^(q^t-1) :=
  rank_tail q (by omega) componentExponent 4 (fun t ht => exponent_double t (by omega))
    (field_tail 4 4 58 29 (by decide) (even_binary 29) (by decide) seed_four q hq) t ht

private theorem field_three (q t : ℕ) (hq : 3≤q) (ht : 5≤t) :
    q^(3*componentExponent t)≤5^(q^t-1) := by
  by_cases he : q=3
  · subst q
    exact rank_tail 3 (by decide) componentExponent 5 (fun t ht => exponent_double t (by omega))
      seed_three t ht
  · exact field_four q t (by omega) (by omega)

theorem common_order_cube (q t : ℕ) (hq : 2≤q) (ht : 2≤t) (hc : Capacity q t) :
    q^(3*componentExponent t)≤5^(q^t-1) := by
  rcases hc with h | ⟨h,h'⟩ | ⟨h,h'⟩ | ⟨h,h'⟩ | h
  · exact field_eleven q t h ht
  · exact field_five q t h h'
  · exact field_four q t h h'
  · exact field_three q t h h'
  · by_cases he : q=2
    · subst q
      exact rank_tail 2 (by decide) componentExponent 8 (fun t ht => exponent_double t (by omega))
        seed_two t h
    · exact field_three q t (by omega) (by omega)

theorem root_power_ge_thirtyTwo (q t : ℕ) (hq : 2≤q) (ht : 2≤t) (hc : Capacity q t) :
    32≤q^t := by
  rcases hc with h | ⟨h,h'⟩ | ⟨h,h'⟩ | ⟨h,h'⟩ | h
  · exact (by decide : 32≤11^2).trans
      ((Nat.pow_le_pow_left h 2).trans (Nat.pow_le_pow_right (by omega) ht))
  · exact (by decide : 32≤5^3).trans
      ((Nat.pow_le_pow_left h 3).trans (Nat.pow_le_pow_right (by omega) h'))
  · exact (by decide : 32≤4^4).trans
      ((Nat.pow_le_pow_left h 4).trans (Nat.pow_le_pow_right (by omega) h'))
  · exact (by decide : 32≤3^5).trans
      ((Nat.pow_le_pow_left h 5).trans (Nat.pow_le_pow_right (by omega) h'))
  · exact (by decide : 32≤2^8).trans
      ((Nat.pow_le_pow_left hq 8).trans (Nat.pow_le_pow_right (by omega) h))

theorem rank_two_order_cube (q : ℕ) (hq : 128≤q) : q^39≤5^(q-1) := by
  by_cases hlarge : 256≤q
  · exact (Nat.pow_le_pow_right (by omega : 0<q) (by decide : 39≤57)).trans
      (WeakClassicalOrderCubeNumerics.symplectic_rank_two_order_cube q hlarge)
  · by_cases hsmall : q≤160
    · exact (Nat.pow_le_pow_left hsmall 39).trans
        ((by norm_num : (160:ℕ)^39≤5^127).trans (Nat.pow_le_pow_right (by decide) (by omega)))
    · exact (Nat.pow_le_pow_left (by omega : q≤256) 39).trans
        ((by norm_num : (256:ℕ)^39≤5^160).trans (Nat.pow_le_pow_right (by decide) (by omega)))

end SymmetricSubgroupAsymptotics.SymplecticSharpOrderCubeNumerics
