import SymmetricSubgroupAsymptotics.OddPrimePowerAffineBlockOrdinaryGeneratorInduction
import SymmetricSubgroupAsymptotics.TernaryBlockOrdinaryGeneratorInduction

/-! The complete odd-degree affine minimal-block branch. Degree three
uses the actual ternary theorem, including full S3 components and tops;
every larger odd degree uses the actual inverse-pair affine compression.
The original point action and strict smaller-section induction are kept. -/
set_option autoImplicit false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics.OddAffineBlockOrdinaryGeneratorInduction

variable (n : ℕ) (J : Subgroup (Equiv.Perm (Fin n)))
    [MulAction.IsPretransitive J (Fin n)] (ω₀ : Fin n)
    (D : OriginalMinimalBlock (A:=J) ω₀)
    (P : PrimitiveAffineProfile D.Component D.Fibre)
    (hbelow : ∀ (k : ℕ), k < n → ∀ L : Subgroup (Equiv.Perm (Fin k)),
      (k = 3 → L ≠ ⊤) → ∃ S : Finset L, Subgroup.closure (S : Set L) = ⊤ ∧ 2*S.card ≤ k)

include P hbelow in
/-- Every actual odd-degree affine block component is covered, without
an exceptional field/degree list or a same-degree generator premise. -/
theorem subgroup_half_degree_generators (hodd : Odd (Nat.card D.Fibre)) :
    ∃ S : Finset J, Subgroup.closure (S : Set J) = ⊤ ∧ 2*S.card ≤ n := by
  letI : Fact P.p.Prime := ⟨P.p_prime⟩
  have htwo := D.degrees_ge_two.1
  letI : Nontrivial D.Fibre := Finite.one_lt_card_iff_nontrivial.mp (by omega)
  letI : Nontrivial D.Points := Finite.one_lt_card_iff_nontrivial.mp (by
    have hh := D.degrees_ge_two.2
    omega)
  by_cases hthree : Nat.card D.Fibre = 3
  · let e : Fin 3 ≃ D.Fibre := (Finite.equivFinOfCardEq hthree).symm
    have hbase : PermutationOrdinarySmallerActions.SmallerActionBound (Nat.card (Fin n)) := by
      simpa only [Nat.card_fin] using
        PermutationOrdinarySmallerActions.smallerActionBound_of_subgroup_generators n hbelow
    have hh := TernaryBlockOrdinaryGeneratorInduction.exists_half_degree_generators
      D.map D.map_equivariant D.base e hbase
    simpa only [Nat.card_fin] using hh
  · have hfive : 5 ≤ Nat.card D.Fibre := by
      have hh := Nat.odd_iff.mp hodd
      omega
    have hp : P.p ≠ 2 := by
      intro hp
      obtain ⟨d,hd⟩ := IsPGroup.exists_card_eq P.V_pgroup
      let origin : D.Fibre := ⟨ω₀,D.map_base⟩
      have heq : Nat.card D.Fibre = 2^d := by rw [←P.card_eq origin,hd,hp]
      have hd0 : d ≠ 0 := by
        intro hz
        rw [hz,pow_zero] at heq
        omega
      have heven : Even (2^d) := Nat.even_pow.mpr ⟨by decide,hd0⟩
      exact (Nat.not_odd_iff_even.mpr heven) (heq ▸ hodd)
    exact OddPrimePowerAffineBlockOrdinaryGeneratorInduction.subgroup_half_degree_generators
      n J ω₀ D P hp hfive hbelow

include hbelow in
/-- Equivalent profile-prime formulation, with oddness of the actual
block degree proved from its regular p-group rather than assumed. -/
theorem subgroup_half_degree_generators_of_odd_prime (hp : P.p ≠ 2) :
    ∃ S : Finset J, Subgroup.closure (S : Set J) = ⊤ ∧ 2*S.card ≤ n := by
  letI : Fact P.p.Prime := ⟨P.p_prime⟩
  let origin : D.Fibre := ⟨ω₀,D.map_base⟩
  obtain ⟨d,hd⟩ := IsPGroup.exists_card_eq P.V_pgroup
  have hodd : Odd (Nat.card D.Fibre) := by
    rw [←P.card_eq origin,hd]
    exact (P.p_prime.odd_of_ne_two hp).pow
  exact subgroup_half_degree_generators n J ω₀ D P hbelow hodd

end SymmetricSubgroupAsymptotics.OddAffineBlockOrdinaryGeneratorInduction
