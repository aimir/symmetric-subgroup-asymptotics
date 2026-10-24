import SymmetricSubgroupAsymptotics.BinaryBlockOrdinaryGeneratorInduction
import SymmetricSubgroupAsymptotics.PermutationStabilizerInduced
import SymmetricSubgroupAsymptotics.InducedMinimumCharacteristicBounds
import SymmetricSubgroupAsymptotics.BinaryChainCentralBinomialBudget

/-! An actual binary block step with an arbitrary original top. The
correlated bit kernel embeds into induction of the trivial line from an
actual point stabilizer. Only the TOP DEGREE is a power of two; the top
group need not be a 2-group and need not have a binary block chain.
No Tracey or McIver--Neumann input is used. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.BinaryBlockCentralBinomialOrdinaryStep
open BinaryChainCentralBinomialBudget

/-- Exact prime-power capacity for the original permutation module. -/
theorem permutation_uniform {G I : Type} [Group G] [Finite G] [Finite I]
    [MulAction G I] [MulAction.IsPretransitive G I]
    (i : I) (k : ℕ) (hcard : Nat.card I = 2^k) :
    UniformSubrepresentationGeneratorBound
      (permutationFunctionRepresentation (ZMod 2) G I) (middle k) := by
  let H : Subgroup G := MulAction.stabilizer G i
  let rho := Representation.trivial (ZMod 2) H (ZMod 2)
  have hi : H.index = 2^k := by
    simpa only [H, MulAction.index_stabilizer_of_transitive] using hcard
  have hc := InducedMinimumUniformCapacity.characteristic_primePower H rho k hi
  have hcR : (InducedMinimumUniformCapacity.capacity H rho : ℝ) ≤
      (2 : ℝ)^k * (middle k : ℝ) / (2 : ℝ)^k := by
    simpa only [Module.finrank_self, Nat.cast_one, one_mul, hi, Nat.cast_pow,
      show (2-1 : ℕ) = 1 from rfl, Nat.mul_one, middle] using hc
  have hp : (2 : ℝ)^k ≠ 0 := pow_ne_zero _ (by norm_num)
  have hcap : InducedMinimumUniformCapacity.capacity H rho ≤ middle k := by
    have heq : (2 : ℝ)^k * (middle k : ℝ) / (2 : ℝ)^k = middle k := by
      rw [mul_comm, mul_div_cancel_right₀ _ hp]
    rw [heq] at hcR
    exact_mod_cast hcR
  have hu := (InducedMinimumUniformCapacity.uniform H rho).of_injective
    (PermutationStabilizerInduced.toInduced (k := ZMod 2) i)
    (PermutationStabilizerInduced.toInduced_injective (k := ZMod 2) i)
  exact hu.mono hcap

variable {Ω I : Type} [Finite Ω] [Finite I]
    {J : Subgroup (Equiv.Perm Ω)} (F : BinaryPairFrame J I)
    [MulAction J I] [MulAction.IsPretransitive J I]
    (hact : ∀ (g : J) (i : I), g • i = F.top g i)

include hact

/-- The ordinary cost of the SAME actual binary kernel is one central
coefficient. Its arbitrary faithful top remains explicitly in the bound. -/
theorem genRank_le_top_add_middle (i : I) (k : ℕ) (hcard : Nat.card I = 2^k) :
    MarkedC4.genRank J ≤ MarkedC4.genRank F.top.range + middle k := by
  let pi : J →* F.top.range := F.top.rangeRestrict
  letI : IsMulCommutative F.top.ker :=
    BinaryBlockOrdinaryGeneratorInduction.kernel_isMulCommutative F
  letI : IsMulCommutative pi.ker := by
    change IsMulCommutative F.top.rangeRestrict.ker
    rw [MonoidHom.ker_rangeRestrict]
    infer_instance
  have hK : MarkedC4.normalGen pi.ker ≤ middle k := by
    change MarkedC4.normalGen F.top.rangeRestrict.ker ≤ middle k
    rw [MonoidHom.ker_rangeRestrict]
    exact F.normalGen_le_of_uniform_pair_module hact (middle k)
      (permutation_uniform i k hcard) F.top.ker le_rfl
  exact (AbelianKernelOrdinaryGeneration.genRank_le_quotient_add_normalGen
    pi F.top.rangeRestrict_surjective).trans (Nat.add_le_add_left hK _)

/-- A chain cost is propagated ONLY after paying the actual smaller top.
The existence of a pure binary chain is not assumed implicitly. -/
theorem genRank_le_cumulative_of_top (i : I) (k : ℕ) (hcard : Nat.card I = 2^k)
    (htop : MarkedC4.genRank F.top.range ≤ cumulative k) :
    MarkedC4.genRank J ≤ cumulative (k+1) := by
  rw [cumulative_succ]
  exact (genRank_le_top_add_middle F hact i k hcard).trans
    (Nat.add_le_add_right htop _)

theorem exists_generating_finset (i : I) (k : ℕ) (hcard : Nat.card I = 2^k) :
    ∃ S : Finset J, Subgroup.closure (S : Set J) = ⊤ ∧
      S.card ≤ MarkedC4.genRank F.top.range + middle k := by
  obtain ⟨S, hcardS, hgen⟩ := MarkedC4.genRank_spec (G := J)
  exact ⟨S, hgen, hcardS.le.trans (genRank_le_top_add_middle F hact i k hcard)⟩

end SymmetricSubgroupAsymptotics.BinaryBlockCentralBinomialOrdinaryStep
