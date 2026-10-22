import SymmetricSubgroupAsymptotics.CFSGIsotypicRepresentationCoordinates
import SymmetricSubgroupAsymptotics.CFSGIsotypicCentralizerOriginalSix
import SymmetricSubgroupAsymptotics.CFSGSmallBinaryLinearSolubility

/-! The actual linear centralizer is soluble for a faithful isotypic
representation of a noncommutative simple group whose binary dimension
divides six. The only constituents have dimension three or six, and the
only repetition beyond irreducibility is the checked twofold dimension-three case. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped Classical MonoidAlgebra IsMulCommutative

namespace SymmetricSubgroupAsymptotics.CFSGIsotypicSimpleCentralizerSix
open CFSGIrreducibleLinearCentralizer CFSGIsotypicRepresentationCoordinates

theorem irreducible_three_centralizer_soluble
    {S V : Type} [Group S] [AddCommGroup V] [Module (ZMod 2) V]
    [Finite V] [FiniteDimensional (ZMod 2) V]
    (rho : Representation (ZMod 2) S V) (hirr : Representation.IsIrreducible rho)
    (hd : Module.finrank (ZMod 2) V = 3) : IsSolvable (linearCentralizer rho) := by
  letI : Representation.IsIrreducible rho := hirr
  letI : Fact (Nat.Prime 7) := ⟨by decide⟩
  have hcard : Nat.card V - 1 = 7 := by
    rw [Module.natCard_eq_pow_finrank (K := ZMod 2), Nat.card_zmod, hd]
    decide
  letI : IsCyclic (linearCentralizer rho) :=
    centralizer_isCyclic_of_prime_nonzero_card rho hcard
  exact isSolvable_of_comm (fun a b => mul_comm a b)

theorem isotypic_simple_centralizer_soluble
    {S V : Type} [Group S] [Finite S] [IsSimpleGroup S]
    [AddCommGroup V] [Module (ZMod 2) V] [Finite V] [Nontrivial V]
    [FiniteDimensional (ZMod 2) V]
    (rho : Representation (ZMod 2) S V) (hf : Function.Injective rho)
    (hnc : ¬ IsMulCommutative S) (hdvd : Module.finrank (ZMod 2) V ∣ 6)
    (hss : IsSemisimpleModule (ZMod 2)[S] rho.asModule)
    (hiso : IsIsotypic (ZMod 2)[S] rho.asModule) :
    IsSolvable (linearCentralizer rho) := by
  obtain ⟨n, U, hn, hirr, e, he⟩ := exists_irreducible_coordinates rho hss hiso
  let tau := U.toRepresentation
  letI : Representation.IsIrreducible tau := hirr
  have hft : Function.Injective tau := constituent_injective_of_coordinates rho tau hf e he
  let d := Module.finrank (ZMod 2) U.toSubmodule
  have hdge : 3 ≤ d :=
    CFSGSmallBinaryLinearSolubility.three_le_dimension_of_noncommutative_simple tau hft hnc
  have hprod : n * d = Module.finrank (ZMod 2) V := by
    have hh := e.finrank_eq.symm
    rw [Module.finrank_pi_fintype] at hh
    simpa only [Finset.sum_const, Finset.card_univ, Fintype.card_fin,
      nsmul_eq_mul, Nat.cast_id] using hh
  have hddiv : d ∣ 6 :=
    (show d ∣ Module.finrank (ZMod 2) V by rw [← hprod]; exact dvd_mul_left _ _).trans hdvd
  have hcases : ∀ j ∈ Nat.divisors 6, j = 1 ∨ j = 2 ∨ j = 3 ∨ j = 6 := by decide +kernel
  have hdcase : d = 3 ∨ d = 6 := by
    rcases hcases d (Nat.mem_divisors.mpr ⟨hddiv, by decide⟩) with h | h | h | h <;> omega
  have hdim : Module.finrank (ZMod 2) V ≤ 6 := Nat.le_of_dvd (by decide) hdvd
  have hnp : n = 1 ∨ (n = 2 ∧ d = 3) := by
    have hnd : n * d ≤ 6 := hprod.le.trans hdim
    by_cases h1 : n = 1
    · exact Or.inl h1
    · right
      have hn2 : 2 ≤ n := by omega
      have hnle : n ≤ 2 := by nlinarith
      have hnEq : n = 2 := by omega
      refine ⟨hnEq, ?_⟩
      rw [hnEq] at hnd
      omega
  rcases hnp with hn1 | ⟨hn2, hd3⟩
  · have hdU : Module.finrank (ZMod 2) U.toSubmodule = Module.finrank (ZMod 2) V := by
      simpa only [hn1, one_mul] using hprod
    have htop : U = ⊤ := by
      apply Subrepresentation.toSubmodule_injective
      exact Submodule.eq_top_of_finrank_eq hdU
    have hrho : Representation.IsIrreducible rho := by
      apply isSimpleOrder_iff_isAtom_top.mpr
      simpa only [htop] using (Subrepresentation.irreducible_iff_isAtom U).mp hirr
    rcases hdcase with hd3 | hd6
    · exact irreducible_three_centralizer_soluble rho hrho (hdU.symm.trans hd3)
    · exact CFSGIsotypicCentralizerOriginalSix.original_irreducible_six_centralizer_soluble
        rho hrho (hdU.symm.trans hd6)
  · subst n
    letI : Nontrivial U.toSubmodule := Subrepresentation.irreducible_module_nontrivial tau
    exact CFSGIsotypicCentralizerOriginalSix.original_twofold_centralizer_soluble
      rho tau e he hirr hft hnc hd3

end SymmetricSubgroupAsymptotics.CFSGIsotypicSimpleCentralizerSix
