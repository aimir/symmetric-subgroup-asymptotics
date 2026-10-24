import SymmetricSubgroupAsymptotics.TransitivePermutationModuleGenerators
import SymmetricSubgroupAsymptotics.BinaryPairKernelNormalGenerators
import SymmetricSubgroupAsymptotics.AbelianKernelOrdinaryGeneration
import SymmetricSubgroupAsymptotics.TransitiveBinaryPairFrame
import SymmetricSubgroupAsymptotics.PermutationOrdinarySmallerActions

/-! The entire binary-block branch of ordinary generator induction.
The correlated original kernel is an actual binary permutation
subrepresentation, not a full flip product. Its ambient normal-generator
bound is used only after proving this actual kernel is abelian.
Rounded smaller-action generation pays even the full S3 top exception.
No split-extension assumption or current-degree generator bound is used. -/
set_option autoImplicit false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics.BinaryBlockOrdinaryGeneratorInduction
open PermutationOrdinarySmallerActions

variable {Ω I : Type} [Finite Ω] [Finite I] {J : Subgroup (Equiv.Perm Ω)}
    (F : BinaryPairFrame J I) [MulAction J I]
    (hact : ∀ (g : J) (i : I), g • i = F.top g i)

omit [Finite Ω] [Finite I] [MulAction J I] in
/-- The ordinary pair kernel is genuinely abelian, so its ambient normal
generators may legitimately be used in the ordinary extension bound. -/
theorem kernel_isMulCommutative : IsMulCommutative F.top.ker where
  is_comm.comm x y := by
    apply F.kernelChart.injective
    simp only [map_mul]
    exact mul_comm _ _

include F hact in
/-- All kernel correlations are retained by the existing faithful bit
chart and the original-conjugation equivariant module inclusion. -/
theorem normalGen_kernel_le_half [Nontrivial I] [MulAction.IsPretransitive J I] :
    MarkedC4.normalGen F.top.ker ≤ Nat.card I / 2 := by
  exact F.normalGen_le_of_uniform_pair_module hact (Nat.card I / 2)
    (TransitivePermutationModuleGenerators.uniform_of_transitive (ZMod 2))
    F.top.ker le_rfl

include F hact in
/-- Every original binary pair frame with a transitive nontrivial top
satisfies the sharp ordinary bound under strictly smaller induction. -/
theorem half_degree_of_frame [Nontrivial I] [MulAction.IsPretransitive J I]
    (hbelow : SmallerActionBound (Nat.card Ω)) :
    2 * MarkedC4.genRank J ≤ Nat.card Ω := by
  have hdegree : Nat.card Ω = 2 * Nat.card I := by
    have hh := Nat.card_congr F.frame
    rw [Nat.card_prod,Nat.card_zmod] at hh
    exact hh.symm.trans (Nat.mul_comm _ _)
  have htwo : 2 ≤ Nat.card I := by
    have hh : 1 < Nat.card I := Finite.one_lt_card_iff_nontrivial.mpr inferInstance
    omega
  have hlt : Nat.card I < Nat.card Ω := by omega
  let π : J →* F.top.range := F.top.rangeRestrict
  have hπ : Function.Surjective π := F.top.rangeRestrict_surjective
  letI : Finite F.top.range := Finite.of_surjective π hπ
  have hQ := rounded_rank_of_smaller (Nat.card Ω) hbelow F.top.range I hlt
  letI : IsMulCommutative F.top.ker := kernel_isMulCommutative F
  letI : IsMulCommutative π.ker := by
    change IsMulCommutative F.top.rangeRestrict.ker
    rw [MonoidHom.ker_rangeRestrict]
    infer_instance
  have hG := AbelianKernelOrdinaryGeneration.genRank_le_quotient_add_normalGen π hπ
  have hK : MarkedC4.normalGen π.ker ≤ Nat.card I / 2 := by
    change MarkedC4.normalGen F.top.rangeRestrict.ker ≤ Nat.card I / 2
    rw [MonoidHom.ker_rangeRestrict]
    exact normalGen_kernel_le_half F hact
  omega

include F hact in
theorem exists_half_degree_generators [Nontrivial I] [MulAction.IsPretransitive J I]
    (hbelow : SmallerActionBound (Nat.card Ω)) :
    ∃ S : Finset J, Subgroup.closure (S : Set J) = ⊤ ∧ 2 * S.card ≤ Nat.card Ω := by
  obtain ⟨S,hS,hgen⟩ := MarkedC4.genRank_spec (G:=J)
  exact ⟨S,hgen,by rw [hS]; exact half_degree_of_frame F hact hbelow⟩

/-- The literal subgroup installer uses a cover in its original subgroup
lattice and the original coset action on the resulting binary blocks. -/
theorem subgroup_half_degree_generators (n : ℕ) (U : Subgroup (Equiv.Perm (Fin n)))
    (htrans : MulAction.IsPretransitive U (Fin n)) (ω₀ : Fin n)
    (D : TransitiveBinaryPairCover U ω₀) (hproper : D.subgroup < ⊤)
    (hbelow : ∀ (k : ℕ), k < n → ∀ L : Subgroup (Equiv.Perm (Fin k)),
      (k = 3 → L ≠ ⊤) → ∃ S : Finset L, Subgroup.closure (S : Set L) = ⊤ ∧ 2 * S.card ≤ k) :
    ∃ S : Finset U, Subgroup.closure (S : Set U) = ⊤ ∧ 2 * S.card ≤ n := by
  letI : MulAction.IsPretransitive U (Fin n) := htrans
  have htwo : 2 ≤ Nat.card D.Points := by
    have hh : 1 < D.subgroup.index := Subgroup.one_lt_index_of_ne_top hproper.ne
    exact hh
  letI : Nontrivial D.Points := Finite.one_lt_card_iff_nontrivial.mp (by omega)
  have hbase : SmallerActionBound (Nat.card (Fin n)) := by
    simpa only [Nat.card_fin] using smallerActionBound_of_subgroup_generators n hbelow
  have hh := exists_half_degree_generators D.frame (fun _ _ => rfl) hbase
  simpa only [Nat.card_fin] using hh

end SymmetricSubgroupAsymptotics.BinaryBlockOrdinaryGeneratorInduction
