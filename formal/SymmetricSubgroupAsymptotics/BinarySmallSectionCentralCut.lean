import SymmetricSubgroupAsymptotics.BinaryDisplacementCentralCut
import SymmetricSubgroupAsymptotics.BinaryCentralCutNumerics

/-! The ordinary evaluation separator gives a strict actual central-cut
cost for every small original binary permutation section of power degree
at least sixteen. There is no exceptional finite action list. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics

variable {G X A : Type} [Group G] [MulAction G X]
    [Finite G] [Finite X] [MulAction.IsPretransitive G X]
    [AddCommGroup A] [Module (ZMod 2) A] [FiniteDimensional (ZMod 2) A]

theorem binary_small_permutationSection_exists_central_cut
    (ρ : Representation (ZMod 2) G A) (hG : IsPGroup 2 G)
    (M : Subrepresentation (permutationFunctionRepresentation (ZMod 2) G X))
    (q : M.toRepresentation.IntertwiningMap ρ) (hq : Function.Surjective q)
    (x : X) (a : ℕ) (ha : 4≤a) (hdegree : Nat.card X=2^a)
    (hsmall : 2*Module.finrank (ZMod 2) A≤2^a) :
    ∃ (C : Submodule (ZMod 2) A) (hC : C≤ρ.invariants),
      displacementSlice ρ C=⊥ ∧
      2*Module.finrank (ZMod 2) C +
        4*Module.finrank (ZMod 2) (centralQuotientRepresentation ρ C hC).invariants+2 ≤
          2^a := by
  obtain ⟨C,hC,hzero,hcost⟩ := binary_permutationSection_exists_central_cut
    ρ hG M q hq x a (by omega) hdegree
  refine ⟨C,hC,hzero,?_⟩
  have hD := binary_previous_middle_budget a ha
  have hlarge : 16≤2^a := Nat.pow_le_pow_right (by decide : 1≤2) ha
  have heven : 2^a=2*2^(a-1) := by
    calc
      2^a=2^((a-1)+1) := by rw [Nat.sub_add_cancel (by omega : 1≤a)]
      _=2*2^(a-1) := by rw [pow_succ,Nat.mul_comm]
  omega

theorem binary_small_permutationSection_exists_central_cut_capacity
    (ρ : Representation (ZMod 2) G A) (hG : IsPGroup 2 G)
    (M : Subrepresentation (permutationFunctionRepresentation (ZMod 2) G X))
    (q : M.toRepresentation.IntertwiningMap ρ) (hq : Function.Surjective q)
    (x : X) (a : ℕ) (ha : 4≤a) (hdegree : Nat.card X=2^a)
    (hsmall : 2*Module.finrank (ZMod 2) A≤2^a) :
    ∃ (C : Submodule (ZMod 2) A) (hC : C≤ρ.invariants),
      (2:ℝ)*Module.finrank (ZMod 2) C +
        4*representationSchurCapacity (centralQuotientRepresentation ρ C hC)+2 ≤
          (2:ℝ)^a := by
  obtain ⟨C,hC,_,hcost⟩ := binary_small_permutationSection_exists_central_cut
    ρ hG M q hq x a ha hdegree hsmall
  letI : Finite A := Finite.of_surjective q hq
  letI : Finite (A ⧸ C) := Finite.of_surjective C.mkQ C.mkQ_surjective
  refine ⟨C,hC,?_⟩
  rw [pGroup_representationSchurCapacity hG]
  exact_mod_cast hcost

end SymmetricSubgroupAsymptotics
