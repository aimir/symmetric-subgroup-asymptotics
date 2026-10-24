import SymmetricSubgroupAsymptotics.QuadraticRankOrderCubeNumerics

/-! One component exponent covers actual B/D/twisted-D bilinear order
bounds at their unchanged root-star dimensions. All seeds are small
scalar comparisons followed by the existing field/rank inductions. -/
set_option autoImplicit false
namespace SymmetricSubgroupAsymptotics.OrthogonalBilinearOrderCubeNumerics
open QuadraticRankOrderCubeNumerics

def componentExponent (t : ℕ) : ℕ := 2*(t+2)^2+(t+2)+6

def Capacity (q t : ℕ) : Prop :=
  16≤q ∨ (7≤q ∧ 3≤t) ∨ (4≤q ∧ 4≤t) ∨ (3≤q ∧ 5≤t) ∨ 9≤t

private theorem exponent_double (t : ℕ) (ht : 2≤t) :
    componentExponent (t+1)≤2*componentExponent t := by
  unfold componentExponent
  nlinarith

private theorem binary_even (b : ℕ) : (2:ℕ)^(2*b)≤5^b := by
  rw [pow_mul]
  exact Nat.pow_le_pow_left (by decide) b

private theorem seed_sixteen : (16:ℕ)^(3*componentExponent 2)≤5^(16^2-1) := by
  change (16:ℕ)^126≤5^255
  calc
    (16:ℕ)^126=(2:ℕ)^504 := by rw [show (16:ℕ)=2^4 by decide, ←pow_mul]
    _ ≤5^252 := binary_even 252
    _ ≤5^255 := Nat.pow_le_pow_right (by decide) (by decide)

private theorem seed_seven : (7:ℕ)^(3*componentExponent 3)≤5^(7^3-1) := by
  change (7:ℕ)^183≤5^342
  calc
    (7:ℕ)^183≤7^184 := Nat.pow_le_pow_right (by decide) (by decide)
    _ =(7^2)^92 := by rw [←pow_mul]
    _ ≤(5^3)^92 := Nat.pow_le_pow_left (by decide : (7:ℕ)^2≤5^3) 92
    _ =5^276 := by rw [←pow_mul]
    _ ≤5^342 := Nat.pow_le_pow_right (by decide) (by decide)

private theorem seed_four : (4:ℕ)^(3*componentExponent 4)≤5^(4^4-1) := by
  change (4:ℕ)^252≤5^255
  exact (Nat.pow_le_pow_left (by decide : (4:ℕ)≤5) 252).trans
    (Nat.pow_le_pow_right (by decide) (by decide))

private theorem seed_three : (3:ℕ)^(3*componentExponent 5)≤5^(3^5-1) := by
  change (3:ℕ)^333≤5^242
  calc
    (3:ℕ)^333≤3^338 := Nat.pow_le_pow_right (by decide) (by decide)
    _ =(3^13)^26 := by rw [←pow_mul]
    _ ≤(5^9)^26 := Nat.pow_le_pow_left (by decide : (3:ℕ)^13≤5^9) 26
    _ =5^234 := by rw [←pow_mul]
    _ ≤5^242 := Nat.pow_le_pow_right (by decide) (by decide)

private theorem seed_two : (2:ℕ)^(3*componentExponent 9)≤5^(2^9-1) := by
  change (2:ℕ)^777≤5^511
  exact (Nat.pow_le_pow_right (by decide : 0<2) (by decide : 777≤778)).trans
    ((binary_even 389).trans (Nat.pow_le_pow_right (by decide) (by decide)))

private theorem field_sixteen (q t : ℕ) (hq : 16≤q) (ht : 2≤t) :
    q^(3*componentExponent t)≤5^(q^t-1) :=
  rank_tail q (by omega) componentExponent 2 exponent_double
    (field_tail 16 2 42 21 (by decide) (binary_even 21) (by decide) seed_sixteen q hq) t ht

private theorem field_seven (q t : ℕ) (hq : 7≤q) (ht : 3≤t) :
    q^(3*componentExponent t)≤5^(q^t-1) :=
  rank_tail q (by omega) componentExponent 3 (fun t ht => exponent_double t (by omega))
    (field_tail 7 3 61 31 (by decide)
      ((Nat.pow_le_pow_right (by decide : 0<2) (by decide : 61≤62)).trans (binary_even 31))
      (by decide) seed_seven q hq) t ht

private theorem field_four (q t : ℕ) (hq : 4≤q) (ht : 4≤t) :
    q^(3*componentExponent t)≤5^(q^t-1) :=
  rank_tail q (by omega) componentExponent 4 (fun t ht => exponent_double t (by omega))
    (field_tail 4 4 84 42 (by decide) (binary_even 42) (by decide) seed_four q hq) t ht

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
  · exact field_sixteen q t h ht
  · exact field_seven q t h h'
  · exact field_four q t h h'
  · exact field_three q t h h'
  · by_cases he : q=2
    · subst q
      exact rank_tail 2 (by decide) componentExponent 9 (fun t ht => exponent_double t (by omega))
        seed_two t h
    · exact field_three q t (by omega) (by omega)

theorem root_power_ge_thirtyTwo (q t : ℕ) (hq : 2≤q) (ht : 2≤t) (hc : Capacity q t) :
    32≤q^t := by
  rcases hc with h | ⟨h,h'⟩ | ⟨h,h'⟩ | ⟨h,h'⟩ | h
  · exact (by decide : 32≤16^2).trans
      ((Nat.pow_le_pow_left h 2).trans (Nat.pow_le_pow_right (by omega) ht))
  · exact (by decide : 32≤7^3).trans
      ((Nat.pow_le_pow_left h 3).trans (Nat.pow_le_pow_right (by omega) h'))
  · exact (by decide : 32≤4^4).trans
      ((Nat.pow_le_pow_left h 4).trans (Nat.pow_le_pow_right (by omega) h'))
  · exact (by decide : 32≤3^5).trans
      ((Nat.pow_le_pow_left h 5).trans (Nat.pow_le_pow_right (by omega) h'))
  · exact (by decide : 32≤2^9).trans
      ((Nat.pow_le_pow_left hq 9).trans (Nat.pow_le_pow_right (by omega) h))

def SmallParameters (q t : ℕ) : Prop :=
  (t=2 ∧ q≤15) ∨ (t=3 ∧ q≤6) ∨ (t=4 ∧ q≤3) ∨ (5≤t ∧ t≤8 ∧ q=2)

theorem smallParameters_of_not_capacity (q t : ℕ) (hq : 2≤q) (ht : 2≤t)
    (hc : ¬Capacity q t) : SmallParameters q t := by
  unfold Capacity at hc
  unfold SmallParameters
  omega

end SymmetricSubgroupAsymptotics.OrthogonalBilinearOrderCubeNumerics
