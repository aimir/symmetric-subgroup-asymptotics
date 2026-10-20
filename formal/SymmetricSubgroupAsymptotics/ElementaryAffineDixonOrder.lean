import SymmetricSubgroupAsymptotics.PrimitiveAffineDimensionOrder
import SymmetricSubgroupAsymptotics.SolublePrimitiveOrderBound
import Mathlib.Data.Nat.Log

/-! The large affine step in Dixon's order bound only needs elementary
linear-map counting. No soluble linear base theorem is required. -/
set_option autoImplicit false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics.ElementaryDixonOrderProof
open Non2UnipotentPrefixFiniteMenu

theorem quadratic_log_bound (k : ℕ) (hk : 5 ≤ k) :
    3 * (k+1)^2 ≤ 4 * (2^k-1) := by
  induction k, hk using Nat.le_induction with
  | base => decide +kernel
  | succ k hk ih =>
    have hp : 1 ≤ 2^k := Nat.one_le_pow _ _ (by decide)
    have he : 2^(k+1)-1 = 2*(2^k-1)+1 := by rw [pow_succ];omega
    rw [he]
    have hpoly : (k+2)^2 ≤ 2*(k+1)^2 := by nlinarith
    nlinarith

theorem degree_dimension_cubic_bound (n d : ℕ) (hn : 32 ≤ n)
    (hd : 2^d ≤ n) : (n^(d+1))^3 ≤ 24^(n-1) := by
  let k := Nat.log 2 n
  have hk : 5 ≤ k := Nat.le_log_of_pow_le (by decide) hn
  have hdk : d ≤ k := Nat.le_log_of_pow_le (by decide) hd
  have hnk : n ≤ 2^(k+1) := (Nat.lt_pow_succ_log_self (by decide : 1 < 2) n).le
  have hkn : 2^k ≤ n := Nat.pow_log_le_self 2 (by omega)
  calc
    (n^(d+1))^3 ≤ ((2^(k+1))^(k+1))^3 := by
      apply Nat.pow_le_pow_left _ 3
      exact (Nat.pow_le_pow_left hnk _).trans
        (Nat.pow_le_pow_right (by positivity) (by omega))
    _ = 2^(3*(k+1)^2) := by rw [← pow_mul,← pow_mul];congr 1;ring
    _ ≤ 2^(4*(n-1)) := Nat.pow_le_pow_right (by decide)
      ((quadratic_log_bound k hk).trans (by omega))
    _ = 16^(n-1) := by rw [show 16=2^4 by norm_num,pow_mul]
    _ ≤ 24^(n-1) := Nat.pow_le_pow_left (by decide) _

theorem affine_cubic_order
    (G X : Type) [Group G] [Finite G] [Finite X] [MulAction G X]
    [FaithfulSMul G X] [MulAction.IsPreprimitive G X] [Nontrivial X]
    (P : PrimitiveAffineProfile G X) (hn : 32 ≤ Nat.card X) :
    Nat.card G ^ 3 ≤ 24^(Nat.card X-1) := by
  let C := P.elementaryChart (inferInstance : MulAction.IsPreprimitive G X)
  letI : Fact P.p.Prime := C.primeFact
  letI : Finite C.V := Finite.of_injective
    (fun v : C.V => C.equiv.symm (Multiplicative.ofAdd v))
    (C.equiv.symm.injective.comp Multiplicative.ofAdd.injective)
  let x : X := Classical.arbitrary X
  have hd : 2 ^ Module.finrank (ZMod P.p) C.V ≤ Nat.card X := by
    exact (Nat.pow_le_pow_left P.p_prime.two_le _).trans_eq
      (P.degree_eq_prime_pow_finrank C.equiv x).symm
  exact (Nat.pow_le_pow_left (P.card_le_degree_pow_finrank_succ C.equiv x) 3).trans
    (degree_dimension_cubic_bound _ _ hn hd)

theorem primitive_order
    (catalogue : PublishedPrimitiveCompositionCatalogueCorrespondence)
    (hstructure : PrimitiveSocleRawStructure.PublishedONanScottStructure)
    (G X : Type) [Group G] [Finite G] [Finite X] [MulAction G X]
    [FaithfulSMul G X] [MulAction.IsPreprimitive G X] [Nontrivial X]
    [IsSolvable G] : Nat.card G ^ 3 ≤ 24^(Nat.card X-1) := by
  by_cases hn : Nat.card X < 45
  · exact SolublePermutationOrderProof.bounded_primitive_order catalogue G X hn
  obtain ⟨D⟩ := hstructure G X
  cases D with
  | inl D =>
    let i : Fin D.factorCount := ⟨0,D.factorCount_pos⟩
    let f : finiteGroupSocle G →* D.Simple :=
      (Pi.evalMonoidHom (fun _ : Fin D.factorCount => D.Simple) i).comp
        D.socleEquiv.toMonoidHom
    have hf : Function.Surjective f := by
      intro s
      exact ⟨D.socleEquiv.symm (fun _ => s),by simp [f]⟩
    have hs : IsSolvable D.Simple := solvable_of_surjective hf
    exact (D.noncommutative ⟨⟨IsSimpleGroup.comm_iff_isSolvable.mpr hs⟩⟩).elim
  | inr P => exact affine_cubic_order G X P (by omega)

end SymmetricSubgroupAsymptotics.ElementaryDixonOrderProof
