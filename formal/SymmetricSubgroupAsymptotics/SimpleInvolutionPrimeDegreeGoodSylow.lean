import SymmetricSubgroupAsymptotics.PrimeDegreeFactorialMultiplicity
import SymmetricSubgroupAsymptotics.SimpleInvolutionPrimeCycleGoodSylow
import SymmetricSubgroupAsymptotics.SimplePrimeSylowIndexSquare
import Mathlib.Data.Finite.Perm

/-! Faithful prime/next-prime degree supplies prime-square nondivisibility
internally. These wrappers require no numerical source-order bound. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics.PrimeDegreeFactorialMultiplicity

theorem source_card_prime_square_not_dvd
    {G : Type*} [Group G] [Finite G] {p n : ℕ} [Fact p.Prime]
    [MulAction G (Fin n)] [FaithfulSMul G (Fin n)]
    (hn : n=p ∨ n=p+1) : ¬p^2 ∣ Nat.card G := by
  have hd := Subgroup.card_dvd_of_injective
    (MulAction.toPermHom G (Fin n)) MulAction.toPerm_injective
  rw [Nat.card_perm,Nat.card_fin] at hd
  intro hh
  exact prime_square_not_dvd_degree_factorial p n Fact.out hn (hh.trans hd)

end SymmetricSubgroupAsymptotics.PrimeDegreeFactorialMultiplicity

namespace SymmetricSubgroupAsymptotics.SimpleInvolutionPrimeCycleGoodSylow

theorem goodSylowPrime_of_prime_degree
    {G : Type*} [Group G] [Finite G] [IsSimpleGroup G]
    {p n : ℕ} [Fact p.Prime] [MulAction G (Fin n)] [FaithfulSMul G (Fin n)]
    (x y : G) (hx : x^2=1) (hgen : Subgroup.closure ({x,y} : Set G) = ⊤)
    (hn : n=p ∨ n=p+1)
    (htype : (MulAction.toPermHom G (Fin n) (x*y)).cycleType = {p}) :
    CFSGReduction.GoodSylowPrime G p :=
  goodSylowPrime x y hx hgen hn
    (PrimeDegreeFactorialMultiplicity.source_card_prime_square_not_dvd hn) htype

end SymmetricSubgroupAsymptotics.SimpleInvolutionPrimeCycleGoodSylow

namespace SymmetricSubgroupAsymptotics.SimplePrimeSylowIndexSquare
open PrimitiveSocleRawStructure

theorem least_index_square_of_prime_cycle
    {G : Type} [Group G] [Finite G] [IsSimpleGroup G]
    {p : ℕ} [Fact p.Prime] [MulAction G (Fin p)] [FaithfulSMul G (Fin p)]
    (hn : ¬IsMulCommutative G) (g : G)
    (htype : (MulAction.toPermHom G (Fin p) g).cycleType = {p})
    (ell : ℕ) (hell : LeastProperIndex G ell) : ell^2 < Nat.card G := by
  let rho := MulAction.toPermHom G (Fin p)
  have hperm : orderOf (rho g) = p := by
    change orderOf (MulAction.toPermHom G (Fin p) g) = p
    rw [←Equiv.Perm.lcm_cycleType,htype]
    simp
  have ho : orderOf g = p :=
    (orderOf_injective rho MulAction.toPerm_injective g).symm.trans hperm
  have hU : IsPGroup p (Subgroup.zpowers g) := by
    apply IsPGroup.of_card (n := 1)
    rw [Nat.card_zpowers,ho,pow_one]
  obtain ⟨P,hP⟩ := hU.exists_le_sylow
  have hgP : g ∈ P := hP (Subgroup.mem_zpowers g)
  have hcard : Nat.card P = p :=
    SimpleInvolutionPrimeCycleGoodSylow.sylow_card_of_member_order P g hgP ho
      (PrimeDegreeFactorialMultiplicity.source_card_prime_square_not_dvd (Or.inl rfl))
  have hex : ∃ i : Fin p, rho g i ≠ i := by
    by_contra h
    have he : rho g = 1 := by
      apply Equiv.Perm.ext
      intro i
      change rho g i = i
      by_contra hi
      exact h ⟨i,hi⟩
    rw [he,orderOf_one] at hperm
    have := (Fact.out : Nat.Prime p).two_le
    omega
  obtain ⟨i,hi⟩ := hex
  exact least_index_square_of_moved_point hn P hcard g i hi ell hell

end SymmetricSubgroupAsymptotics.SimplePrimeSylowIndexSquare
