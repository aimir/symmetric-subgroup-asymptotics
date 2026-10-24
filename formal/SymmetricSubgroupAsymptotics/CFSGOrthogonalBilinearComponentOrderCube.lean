import SymmetricSubgroupAsymptotics.PrimitiveSocleRawChart
import SymmetricSubgroupAsymptotics.CFSGOrthogonalBilinearOrderUpper
import SymmetricSubgroupAsymptotics.CFSGOrthogonalBBilinearOrderUpper
import SymmetricSubgroupAsymptotics.OrthogonalBilinearOrderCubeNumerics
import SymmetricSubgroupAsymptotics.CFSGOrthogonalBProperIndexOrderBudget
import SymmetricSubgroupAsymptotics.CFSGOrthogonalDProperIndexOrderBudget
import SymmetricSubgroupAsymptotics.CFSGTwistedDProperIndexOrderBudget
import SymmetricSubgroupAsymptotics.CFSGOrthogonalBSimpleIndexBounds
import SymmetricSubgroupAsymptotics.CFSGOrthogonalDIndexSquare
import SymmetricSubgroupAsymptotics.CFSGTwistedDIndexSquare

/-! Improved component cubes for the SAME original B/D/twisted-D
models, with unchanged proper-index stars and already proved outer
bounds. The actual squared least-index bounds also give the order
threshold needed by the raw socle power form. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGOrthogonalBilinearComponentOrderCube
open PrimitiveSocleRawStructure CFSGReduction OrthogonalBilinearOrderCubeNumerics

private theorem field_two_le (q : CFSG.PrimePower) : 2≤q.order :=
  q.prime_isPrime.two_le.trans (Nat.le_self_pow (Nat.ne_of_gt q.exponent_pos) q.prime)

private theorem exponent_le_field (q : CFSG.PrimePower) : q.exponent≤q.order :=
  q.exponent.lt_two_pow_self.le.trans (Nat.pow_le_pow_left q.prime_isPrime.two_le q.exponent)

private theorem three_exponent_le (q : CFSG.PrimePower) : 3*q.exponent≤q.order^3 := by
  have hc : 3≤q.order^2 := (by decide : 3≤2^2).trans (Nat.pow_le_pow_left (field_two_le q) 2)
  exact (Nat.mul_le_mul hc (exponent_le_field q)).trans_eq (pow_succ q.order 2).symm

private theorem twentyFour_exponent_le (q : CFSG.PrimePower) : 24*q.exponent≤q.order^6 := by
  have hc : 24≤q.order^5 := (by decide : 24≤2^5).trans (Nat.pow_le_pow_left (field_two_le q) 5)
  exact (Nat.mul_le_mul hc (exponent_le_field q)).trans_eq (pow_succ q.order 5).symm

theorem typeB_component_le_field_power (r : ℕ) (hr : 3≤r) (q : CFSG.PrimePower)
    [IsSimpleGroup (CFSG.Models.B r q)] :
    Nat.card (CFSG.Models.B r q)*Nat.card (Outer (CFSG.Models.B r q))≤
      q.order^(2*r^2+3*r+4) := by
  have hb := Nat.mul_le_mul
    (CFSGOrthogonalBBilinearOrderUpper.typeB_order_le_bilinear_power r hr q)
    ((CFSGOrthogonalBOriginalMatrixBounds.typeB_outer_card_le_three_exponent r hr q).trans
      (three_exponent_le q))
  rw [← pow_add] at hb
  exact hb

theorem typeD_component_le_field_power (r : ℕ) (hr : 4≤r) (q : CFSG.PrimePower)
    [IsSimpleGroup (CFSG.Models.D r q)] :
    Nat.card (CFSG.Models.D r q)*Nat.card (Outer (CFSG.Models.D r q))≤
      q.order^(2*r^2+r+6) :=
  (Nat.mul_le_mul (CFSGOrthogonalBilinearOrderUpper.typeD_order_le_bilinear_power r hr q)
    ((CFSGOrthogonalDProperIndexOrderBudget.typeD_outer_card_le_twentyFour_exponent r hr q).trans
      (twentyFour_exponent_le q))).trans_eq (pow_add _ _ _).symm

theorem typeTwistedD_component_le_field_power (r : ℕ) (hr : 4≤r) (q : CFSG.PrimePower)
    [IsSimpleGroup (CFSG.Models.TwistedD r q)]
    (hn : ¬IsMulCommutative (CFSG.Models.TwistedD r q)) :
    Nat.card (CFSG.Models.TwistedD r q)*Nat.card (Outer (CFSG.Models.TwistedD r q))≤
      q.order^(2*r^2+r+4) :=
  (Nat.mul_le_mul (CFSGOrthogonalBilinearOrderUpper.typeTwistedD_order_le_bilinear_power r hr q)
    (CFSGTwistedDProperIndexOrderBudget.typeTwistedD_outer_card_le_field_fourth r hr q hn)).trans_eq
      (pow_add _ _ _).symm

private theorem cube_of_exponent (q : CFSG.PrimePower) (t e a : ℕ) (ht : 2≤t)
    (hc : Capacity q.order t) (ha : a≤q.order^e) (he : e≤componentExponent t) :
    a^3≤5^(q.order^t-1) := by
  have hp := Nat.pow_le_pow_left (ha.trans
    (Nat.pow_le_pow_right (by have h := field_two_le q; omega) he)) 3
  rw [← pow_mul, Nat.mul_comm (componentExponent t) 3] at hp
  exact hp.trans (common_order_cube q.order t (field_two_le q) ht hc)

theorem typeB_component_order_cube (r : ℕ) (hr : 3≤r) (q : CFSG.PrimePower)
    [IsSimpleGroup (CFSG.Models.B r q)] (hc : Capacity q.order (r-1)) :
    (Nat.card (CFSG.Models.B r q)*Nat.card (Outer (CFSG.Models.B r q)))^3≤
      5^(q.order^(r-1)-1) := by
  apply cube_of_exponent q (r-1) (2*r^2+3*r+4) _ (by omega) hc
    (typeB_component_le_field_power r hr q)
  have hs : r-1+1=r := by omega
  unfold componentExponent
  nlinarith

theorem typeD_component_order_cube (r : ℕ) (hr : 4≤r) (q : CFSG.PrimePower)
    [IsSimpleGroup (CFSG.Models.D r q)] (hc : Capacity q.order (r-1)) :
    (Nat.card (CFSG.Models.D r q)*Nat.card (Outer (CFSG.Models.D r q)))^3≤
      5^(q.order^(r-1)-1) := by
  apply cube_of_exponent q (r-1) (2*r^2+r+6) _ (by omega) hc
    (typeD_component_le_field_power r hr q)
  have hs : r-1+1=r := by omega
  unfold componentExponent
  nlinarith

theorem typeTwistedD_component_order_cube (r : ℕ) (hr : 4≤r) (q : CFSG.PrimePower)
    [IsSimpleGroup (CFSG.Models.TwistedD r q)]
    (hn : ¬IsMulCommutative (CFSG.Models.TwistedD r q)) (hc : Capacity q.order (r-2)) :
    (Nat.card (CFSG.Models.TwistedD r q)*Nat.card (Outer (CFSG.Models.TwistedD r q)))^3≤
      5^(q.order^(r-2)-1) := by
  apply cube_of_exponent q (r-2) (2*r^2+r+4) _ (by omega) hc
    (typeTwistedD_component_le_field_power r hr q hn)
  have hs : r-2+2=r := by omega
  unfold componentExponent
  nlinarith

private theorem order_ge_1024_of_index_square {S : Type} [Group S]
    [IsSimpleGroup S] (b : ℕ) (hb : 32≤b)
    (hindex : ∀ K : Subgroup S, K≠⊤ → b≤K.index)
    (hsquare : ∀ ell, LeastProperIndex S ell → ell^2<Nat.card S) : 1024≤Nat.card S := by
  obtain ⟨ell,hell⟩ := exists_leastProperIndex S
  obtain ⟨K,hK,hi⟩ := hell.1
  have hlo : 32≤ell := hb.trans (by simpa only [hi] using hindex K hK)
  have hp := Nat.pow_le_pow_left hlo 2
  norm_num only [Nat.reducePow] at hp
  have hs := hsquare ell hell
  omega

theorem typeB_order_ge_1024_of_star (r : ℕ) (hr : 3≤r) (q : CFSG.PrimePower)
    [IsSimpleGroup (CFSG.Models.B r q)] (hstar : 32≤q.order^(r-1)) :
    1024≤Nat.card (CFSG.Models.B r q) := by
  apply order_ge_1024_of_index_square (q.order^(r-1)) hstar
    (CFSGOrthogonalBOriginalMatrixBounds.typeB_field_power_le_proper_index r hr q)
  intro ell hell
  exact (typeB_simpleIndexBounds r hr q ell hell).1

theorem typeD_order_ge_1024_of_star (r : ℕ) (hr : 4≤r) (q : CFSG.PrimePower)
    [IsSimpleGroup (CFSG.Models.D r q)] (hstar : 32≤q.order^(r-1)) :
    1024≤Nat.card (CFSG.Models.D r q) :=
  order_ge_1024_of_index_square (q.order^(r-1)) hstar
    (CFSGOrthogonalDProperIndexOrderBudget.typeD_field_power_le_proper_index r hr q)
    (typeD_leastProperIndex_square_lt_card r q hr)

theorem typeTwistedD_order_ge_1024_of_star (r : ℕ) (hr : 4≤r) (q : CFSG.PrimePower)
    [IsSimpleGroup (CFSG.Models.TwistedD r q)] (hstar : 32≤q.order^(r-2)) :
    1024≤Nat.card (CFSG.Models.TwistedD r q) :=
  order_ge_1024_of_index_square (q.order^(r-2)) hstar
    (CFSGTwistedDProperIndexOrderBudget.typeTwistedD_field_power_le_proper_index r hr q)
    (typeTwistedD_leastProperIndex_square_lt_card r q hr)

end SymmetricSubgroupAsymptotics.CFSGOrthogonalBilinearComponentOrderCube
