import SymmetricSubgroupAsymptotics.RDTNormalFTop31K44
import SymmetricSubgroupAsymptotics.RDTNormalFTop31K45
import SymmetricSubgroupAsymptotics.BinaryDegreeSixteenHighRankTopModels

/-! Complete actual31-top consumer for every original rank-preserving
excess-one normal quotient. The actual source rank identifies its two
possible correlated kernels internally. No source row, split condition,
or finite normal list is supplied by the caller. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.BinaryPairFrame
variable {X : Type} [Finite X] {U : Subgroup (Equiv.Perm X)}
    [MulAction.IsPretransitive U X] (F : BinaryPairFrame U (Fin 8))

theorem top_thirty_one_all_normal_unit
    (hU : IsPGroup 2 U) (hrank : 5 ≤ MarkedC4.genRank U)
    (hH : F.top.range = BinaryEightTop31CoordinateAction.H)
    (N : Subgroup U) [N.Normal] (hNderived : N ≤ commutator U)
    (hAbQ : Nat.card (Abelianization (U ⧸ N)) ≤ 32)
    (hnonab : ¬ ∀ a b : U ⧸ N, a*b=b*a) :
    ∃ W : Subgroup (U ⧸ N), W.Normal ∧
      MarkedC4.ActualNormalFMarkedPeel.commutatorLog W +
        MarkedC4.ActualNormalFMarkedPeel.centralLog W ≤ 8 ∧
      MarkedC4.ActualNormalFMarkedPeel.centralLog W ≤ 4 := by
  letI topThirtyOne_pretransitive : MulAction.IsPretransitive F.top.range (Fin 8) :=
    F.top_pretransitive
  have htopcard : Nat.card F.top.range = 64 :=
    (Nat.card_congr (MulEquiv.subgroupCongr hH).toEquiv).trans BinaryMenuCayley8T31.exact_card
  have htrans : ∀ i j : Fin 8, ∃ t : F.top.range, t.val i = j := by
    intro i j
    exact MulAction.exists_smul_eq F.top.range i j
  have htop : MarkedC4.genRank F.top.range ≤ 3 := by
    by_contra hn
    obtain ⟨c,hc⟩ := BinaryDegreeEightHighRankAction.four_le_genRank_action_conjugate_heisenberg
      F.top.range (F.top_isPGroup hU) htrans (by omega)
    have hh := Nat.card_congr (actionConjugacyEquiv c hc).toEquiv
    rw [htopcard,BinaryMenuCayley8T22.exact_card] at hh
    norm_num at hh
  have hlarge : 2 ≤ MarkedC4.normalGen F.top.ker := by
    have hh := F.genRank_le_actual_pair_kernel_add_top
    omega
  let K := F.literalTopAxis BinaryEightTop31CoordinateAction.H hH F.top.ker
  have hKhead : 1 < Module.finrank (ZMod 2) K.toRepresentation.Coinvariants := by
    change 1 < Module.finrank (ZMod 2)
      (F.literalTopAxis BinaryEightTop31CoordinateAction.H hH F.top.ker).toRepresentation.Coinvariants
    rw [F.literalTopAxis_head,← F.axis_normalGen_eq_coinvariants F.top.ker le_rfl hU]
    omega
  have hspace := BinaryEightTop31HighHeadKernel.high_head_space K hKhead
  have haxis : F.ambientAxis F.top.ker = F.kernelSpace := by
    apply le_antisymm (F.ambientAxis_le_kernelSpace F.top.ker)
    rintro v ⟨a,rfl⟩
    exact (F.bits_mem_ambientAxis F.top.ker a.toMul).mpr a.toMul.property
  rcases hspace with hsmall | hlarge
  · have hK : F.kernelSpace = BinaryRegularEightNaturalRegistry.chart44.space := by
      rw [← haxis]
      simpa only [K,F.literalTopAxis_space] using hsmall
    exact F.top31_kernel44_all_normal_unit hU hrank hH hK N hNderived hAbQ hnonab
  · have hK : F.kernelSpace = BinaryRegularEightNaturalRegistry.chart45.space := by
      rw [← haxis]
      simpa only [K,F.literalTopAxis_space] using hlarge
    exact F.top31_kernel45_all_normal_unit hU hrank hH hK N hNderived hAbQ hnonab
end SymmetricSubgroupAsymptotics.BinaryPairFrame
