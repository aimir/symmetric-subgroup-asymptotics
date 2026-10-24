import SymmetricSubgroupAsymptotics.FourPointBlockSingleKernelOrdinaryInduction
import SymmetricSubgroupAsymptotics.FourPointBlockZeroOddOrdinaryInduction

/-! All actual four-point block actions satisfy the ordinary half-degree
induction step. The three actual odd-layer states are exhaustive. The
only induction hypothesis concerns strictly smaller faithful actions,
with the literal full-S3 exception retained. -/
set_option autoImplicit false
noncomputable section
open scoped Classical
attribute [local instance] Fintype.ofFinite
namespace SymmetricSubgroupAsymptotics.FourPointBlockOrdinaryGeneratorInduction
open FourPointBlockAffineCoordinates FourPointBlockTranslationKernel
open BinaryPlaneWreathActualOddKernel PermutationOrdinarySmallerActions

variable {G Ω X : Type} [Group G] [Finite G] [Finite Ω] [Finite X]
    [MulAction G Ω] [MulAction G X] [MulAction.IsPretransitive G X]
    [FaithfulSMul G Ω]
    (b : Ω → X) (hb : ∀ (g : G) (ω : Ω), b (g • ω) = g • b ω)
    (x₀ : X) (hfour : Nat.card (originalBlockFibre b x₀) = 4)

include b hb x₀ hfour in
/-- No local odd-image predicate or supplied affine chart remains. -/
theorem half_degree [Nontrivial X]
    (hbelow : SmallerActionBound (Nat.card Ω)) :
    2 * MarkedC4.genRank G ≤ Nat.card Ω := by
  by_cases hzero : oddKernel (linearImage b hb x₀ hfour) = ⊥
  · exact FourPointBlockZeroOddOrdinaryInduction.half_degree b hb x₀ hfour hzero hbelow
  · by_cases hsingle : ∀ i : X,
        BinaryPlaneOddKernelMultiplicityUniform.localKernel (linearImage b hb x₀ hfour) i =
          BinaryPlaneOddKernelMultiplicityUniform.localKernel (linearImage b hb x₀ hfour) x₀
    · exact FourPointBlockSingleKernelOrdinaryInduction.half_degree
        b hb x₀ hfour hzero hsingle hbelow
    · obtain ⟨i,hi⟩ := not_forall.mp hsingle
      exact FourPointBlockMultipleKernelOrdinaryInduction.half_degree
        b hb x₀ hfour hzero ⟨i,x₀,hi⟩ hbelow

include b hb x₀ hfour in
theorem exists_half_degree_generators [Nontrivial X]
    (hbelow : SmallerActionBound (Nat.card Ω)) :
    ∃ S : Finset G, Subgroup.closure (S : Set G) = ⊤ ∧ 2 * S.card ≤ Nat.card Ω := by
  obtain ⟨S,hS,hgen⟩ := MarkedC4.genRank_spec (G := G)
  exact ⟨S,hgen,by rw [hS]; exact half_degree b hb x₀ hfour hbelow⟩

/-- Actual original minimal-block installer with finite generating set. -/
theorem subgroup_half_degree_generators (n : ℕ) (J : Subgroup (Equiv.Perm (Fin n)))
    [MulAction.IsPretransitive J (Fin n)] (ω₀ : Fin n)
    (D : OriginalMinimalBlock (A := J) ω₀) (hfour : Nat.card D.Fibre = 4)
    (hbelow : ∀ (k : ℕ), k < n → ∀ L : Subgroup (Equiv.Perm (Fin k)),
      (k = 3 → L ≠ ⊤) → ∃ S : Finset L, Subgroup.closure (S : Set L) = ⊤ ∧ 2 * S.card ≤ k) :
    ∃ S : Finset J, Subgroup.closure (S : Set J) = ⊤ ∧ 2 * S.card ≤ n := by
  letI : Nontrivial D.Points :=
    Finite.one_lt_card_iff_nontrivial.mp (by have h := D.degrees_ge_two; omega)
  have hbase : SmallerActionBound (Nat.card (Fin n)) := by
    simpa only [Nat.card_fin] using smallerActionBound_of_subgroup_generators n hbelow
  have hh := exists_half_degree_generators D.map D.map_equivariant D.base hfour hbase
  simpa only [Nat.card_fin] using hh

end SymmetricSubgroupAsymptotics.FourPointBlockOrdinaryGeneratorInduction
