import SymmetricSubgroupAsymptotics.BlockLocalOrderOrdinaryGeneratorInduction
import SymmetricSubgroupAsymptotics.PrimitiveAffineOrdinaryGeneratorRank
import Mathlib.Tactic.Ring

/-! Every actual binary affine primitive block of dimension at least
seven satisfies the ordinary half-degree induction step, for every top
action. Its component order is derived from the actual regular subgroup
and faithful linear complement. No finite-action catalogue is used. -/
set_option autoImplicit false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics.BinaryAffineBlockOrderTailOrdinaryGenerators

/-- A single induction proves the entire binary dimension tail. -/
theorem dimension_margin (d : ℕ) (hd : 7 ≤ d) : 2*(d^2+d)+2 ≤ 2^d := by
  induction d,hd using Nat.le_induction with
  | base => norm_num
  | succ d hd ih =>
    have hdd := Nat.mul_le_mul_left d (show 2 ≤ d by omega)
    have hstep : 2*((d+1)^2+(d+1))+2 ≤ 2*(2*(d^2+d)+2) := by nlinarith
    calc
      2*((d+1)^2+(d+1))+2 ≤ 2*(2*(d^2+d)+2) := hstep
      _ ≤ 2*2^d := Nat.mul_le_mul_left 2 ih
      _ = 2^(d+1) := by rw [pow_succ,Nat.mul_comm]

section AffineOrder
variable {L Y : Type} [Group L] [Finite L] [Finite Y] [Nontrivial Y]
    [MulAction L Y] [FaithfulSMul L Y] (P : PrimitiveAffineProfile L Y)

/-- The order bound is for this exact original affine group. Its
translation factor and its complement are both derived from P. -/
theorem affine_card_le_prime_pow
    (hprimitive : MulAction.IsPreprimitive L Y) (C : P.ElementaryChart hprimitive)
    (x : Y) : Nat.card L ≤ P.p^(C.d^2+C.d) := by
  letI : Fact P.p.Prime := C.primeFact
  letI : Finite C.V := Finite.of_injective
    (fun v : C.V => C.equiv.symm (Multiplicative.ofAdd v)) C.equiv.symm.injective
  have hdegree : Nat.card Y = P.p^C.d := by
    simpa only [PrimitiveAffineProfile.ElementaryChart.d] using
      P.degree_eq_prime_pow_finrank C.equiv x
  have hV : Nat.card P.V = P.p^C.d := (P.card_eq x).trans hdegree
  have hcomp := P.complement_card_le_prime_pow_dimension_sq hprimitive C x
  calc
    Nat.card L = Nat.card P.V * Nat.card (P.complement x) :=
      (P.isComplement'_complement x).card_mul.symm
    _ ≤ P.p^C.d * P.p^(C.d^2) := Nat.mul_le_mul hV.le hcomp
    _ = P.p^(C.d^2+C.d) := by rw [←pow_add,Nat.add_comm]
end AffineOrder

section Block
variable {G Ω X : Type} [Group G] [Finite G] [Finite Ω] [Finite X]
    [MulAction G Ω] [MulAction G X] [MulAction.IsPretransitive G X]
    [FaithfulSMul G Ω]
    (b : Ω → X) (hb : ∀ (g : G) (ω : Ω), b (g • ω) = g • b ω) (x₀ : X)
    [Nontrivial (originalBlockFibre b x₀)]
    (P : PrimitiveAffineProfile (originalBlockComponent b hb x₀) (originalBlockFibre b x₀))
    (hprimitive : MulAction.IsPreprimitive
      (originalBlockComponent b hb x₀) (originalBlockFibre b x₀))
    (C : P.ElementaryChart hprimitive) (origin : originalBlockFibre b x₀)

include origin in
theorem half_degree (hp : P.p = 2) (hd : 7 ≤ C.d) (ht : 2 ≤ Nat.card X)
    (hbelow : PermutationOrdinarySmallerActions.SmallerActionBound (Nat.card Ω)) :
    2 * MarkedC4.genRank G ≤ Nat.card Ω := by
  letI : Fact P.p.Prime := C.primeFact
  letI : Finite C.V := Finite.of_injective
    (fun v : C.V => C.equiv.symm (Multiplicative.ofAdd v)) C.equiv.symm.injective
  have hcard : Nat.card (originalBlockComponent b hb x₀) ≤ 2^(C.d^2+C.d) := by
    simpa only [hp] using affine_card_le_prime_pow P hprimitive C origin
  have hdegree : Nat.card (originalBlockFibre b x₀) = 2^C.d := by
    calc
      Nat.card (originalBlockFibre b x₀) = P.p^C.d := by
        simpa only [PrimitiveAffineProfile.ElementaryChart.d] using
          P.degree_eq_prime_pow_finrank C.equiv origin
      _ = 2^C.d := congrArg (fun p : ℕ => p^C.d) hp
  have hmargin : 2*(C.d^2+C.d)+2 ≤ Nat.card (originalBlockFibre b x₀) := by
    rw [hdegree]
    exact dimension_margin C.d hd
  exact BlockLocalOrderOrdinaryGeneratorInduction.half_degree b hb x₀
    (C.d^2+C.d) hcard hmargin ht hbelow

include origin in
theorem exists_half_degree_generators (hp : P.p = 2) (hd : 7 ≤ C.d) (ht : 2 ≤ Nat.card X)
    (hbelow : PermutationOrdinarySmallerActions.SmallerActionBound (Nat.card Ω)) :
    ∃ S : Finset G, Subgroup.closure (S : Set G) = ⊤ ∧ 2 * S.card ≤ Nat.card Ω := by
  obtain ⟨S,hS,hgen⟩ := MarkedC4.genRank_spec (G := G)
  exact ⟨S,hgen,by rw [hS]; exact half_degree b hb x₀ P hprimitive C origin hp hd ht hbelow⟩
end Block

/-- Original minimal-block interface: the elementary chart is chosen
inside the proof. The actual degree bound 128 supplies dimension>=7. -/
theorem subgroup_half_degree_generators (n : ℕ) (J : Subgroup (Equiv.Perm (Fin n)))
    [MulAction.IsPretransitive J (Fin n)] (ω₀ : Fin n)
    (D : OriginalMinimalBlock (A := J) ω₀)
    (P : PrimitiveAffineProfile D.Component D.Fibre) (hp : P.p = 2)
    (hlarge : 128 ≤ Nat.card D.Fibre)
    (hbelow : ∀ (k : ℕ), k < n → ∀ L : Subgroup (Equiv.Perm (Fin k)),
      (k = 3 → L ≠ ⊤) →
        ∃ S : Finset L, Subgroup.closure (S : Set L) = ⊤ ∧ 2 * S.card ≤ k) :
    ∃ S : Finset J, Subgroup.closure (S : Set J) = ⊤ ∧ 2 * S.card ≤ n := by
  letI : Nontrivial D.Fibre := Finite.one_lt_card_iff_nontrivial.mp (by omega)
  let C := P.elementaryChart D.component_preprimitive
  let origin : D.Fibre := ⟨ω₀,D.map_base⟩
  letI : Fact P.p.Prime := C.primeFact
  letI : Finite C.V := Finite.of_injective
    (fun v : C.V => C.equiv.symm (Multiplicative.ofAdd v)) C.equiv.symm.injective
  have hdegree : Nat.card D.Fibre = 2^C.d := by
    calc
      Nat.card D.Fibre = P.p^C.d := by
        simpa only [PrimitiveAffineProfile.ElementaryChart.d] using
          P.degree_eq_prime_pow_finrank C.equiv origin
      _ = 2^C.d := congrArg (fun p : ℕ => p^C.d) hp
  have hd : 7 ≤ C.d := (Nat.pow_le_pow_iff_right (by decide : 1 < 2)).mp (by
    calc
      (2 : ℕ)^7 = 128 := by norm_num
      _ ≤ Nat.card D.Fibre := hlarge
      _ = 2^C.d := hdegree)
  have hbase : PermutationOrdinarySmallerActions.SmallerActionBound (Nat.card (Fin n)) := by
    simpa only [Nat.card_fin] using
      PermutationOrdinarySmallerActions.smallerActionBound_of_subgroup_generators n hbelow
  have h := exists_half_degree_generators D.map D.map_equivariant D.base
    P D.component_preprimitive C origin hp hd D.degrees_ge_two.2 hbase
  simpa only [Nat.card_fin] using h

end SymmetricSubgroupAsymptotics.BinaryAffineBlockOrderTailOrdinaryGenerators
