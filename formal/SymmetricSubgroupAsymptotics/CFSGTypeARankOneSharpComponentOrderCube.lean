import SymmetricSubgroupAsymptotics.RankOneSharpOrderCubeNumerics
import SymmetricSubgroupAsymptotics.CFSGTypeARankOneComponentOrderCube
import SymmetricSubgroupAsymptotics.CFSGPSLTwoBorelCardinality

/-! The SAME original PSL2 model has order at most q^3 from its
literal Borel/torus coordinates. Its checked outer bound 2f, retained
instead of replaced by 2q, yields a component budget 8m^4 at the actual
half-field proper index. No subgroup classification is used. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGTypeARankOneSharpComponentOrderCube
open PrimitiveSocleRawStructure CFSGReduction CFSGPSLTwoRootCoordinates CFSGPSLTwoGeometry

theorem projective_card_le_field_cube (F : Type) [Field F] [Finite F] :
    Nat.card (PSL (F:=F))≤Nat.card F^3 := by
  have ht : Nat.card (pairTorus (F:=F))≤Nat.card F-1 := by
    have h := Nat.card_le_card_of_surjective
      (projectiveTorusHom (F:=F)).rangeRestrict (projectiveTorusHom (F:=F)).rangeRestrict_surjective
    simpa only [Nat.card_units] using h
  have hq : 1≤Nat.card F := Nat.card_pos
  have hs : Nat.card F-1+1=Nat.card F := by omega
  rw [projective_card_eq_torus_mul]
  have hh := Nat.mul_le_mul_right (Nat.card F+1)
    (Nat.mul_le_mul_right (Nat.card F) ht)
  rw [← hs] at hh ⊢
  simp only [Nat.add_sub_cancel] at hh
  nlinarith

theorem typeA_rank_one_order_le_cube (q : CFSG.PrimePower) :
    Nat.card (CFSG.Models.A 1 q)≤q.order^3 := by
  simpa only [q.card_field] using projective_card_le_field_cube q.Field

private theorem four_mul_le_two_pow (f : ℕ) (hf : 4≤f) : 4*f≤2^f := by
  induction f, hf using Nat.le_induction with
  | base => decide
  | succ f hf ih =>
    calc
      4*(f+1)≤2*(4*f) := by omega
      _ ≤2*2^f := Nat.mul_le_mul_left 2 ih
      _ =2^(f+1) := (pow_succ' 2 f).symm

theorem twice_outer_card_le_field (q : CFSG.PrimePower) (hq : 16≤q.order) :
    2*Nat.card (Outer (CFSG.Models.A 1 q))≤q.order := by
  have hf : 4*q.exponent≤q.order := by
    by_cases hsmall : q.exponent≤3
    · omega
    · exact (four_mul_le_two_pow q.exponent (by omega)).trans
        (Nat.pow_le_pow_left q.prime_isPrime.two_le q.exponent)
  have ho := CFSGPSLTwoOuterBound.typeA_rank_one_outer_card q
  omega

theorem component_le_of_field_le_twice (q : CFSG.PrimePower) (hq : 16≤q.order)
    (m : ℕ) (hqm : q.order≤2*m) :
    Nat.card (CFSG.Models.A 1 q)*Nat.card (Outer (CFSG.Models.A 1 q))≤8*m^4 := by
  have ho : Nat.card (Outer (CFSG.Models.A 1 q)) ≤ m := by
    have h := twice_outer_card_le_field q hq
    omega
  calc
    _ ≤q.order^3*m := Nat.mul_le_mul (typeA_rank_one_order_le_cube q) ho
    _ ≤(2*m)^3*m := Nat.mul_le_mul_right _ (Nat.pow_le_pow_left hqm 3)
    _ =8*m^4 := by ring

theorem component_order_cube (q : CFSG.PrimePower) (hq : 64≤q.order) :
    (Nat.card (CFSG.Models.A 1 q)*Nat.card (Outer (CFSG.Models.A 1 q)))^3≤
      5^((q.order+1)/2-1) := by
  have hm : 32≤(q.order+1)/2 := by omega
  have hqm : q.order≤2*((q.order+1)/2) := by omega
  exact (Nat.pow_le_pow_left (component_le_of_field_le_twice q (by omega) _ hqm) 3).trans
    (RankOneSharpOrderCubeNumerics.order_cube_le _ hm)

theorem order_ge_1024 (q : CFSG.PrimePower) (hq : 64≤q.order)
    [IsSimpleGroup (CFSG.Models.A 1 q)] : 1024≤Nat.card (CFSG.Models.A 1 q) := by
  obtain ⟨ell,hell⟩ := exists_leastProperIndex (CFSG.Models.A 1 q)
  have hfield : q.order≤2*ell := by
    simpa only [q.card_field] using
      CFSGPSLTwoGeometry.field_card_le_twice_leastProperIndex (F:=q.Field) ell hell
  have hlo : 32≤ell := by omega
  have hs := CFSGPSLTwoGeometry.leastProperIndex_square_lt_card (F:=q.Field)
    (by rw [q.card_field]; omega) ell hell
  change ell^2<Nat.card (CFSG.Models.A 1 q) at hs
  have hp := Nat.pow_le_pow_left hlo 2
  norm_num only [Nat.reducePow] at hp
  omega

end SymmetricSubgroupAsymptotics.CFSGTypeARankOneSharpComponentOrderCube
