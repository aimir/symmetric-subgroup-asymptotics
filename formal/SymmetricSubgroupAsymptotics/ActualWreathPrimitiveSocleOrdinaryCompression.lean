import SymmetricSubgroupAsymptotics.ActualWreathIsotypicNonabelianOrdinaryStep
import SymmetricSubgroupAsymptotics.PrimitiveSocleIsotypicOrdinaryCompression
import SymmetricSubgroupAsymptotics.PrimitiveSocleRawOneFactor
import SymmetricSubgroupAsymptotics.WreathCompressionQuotientComposition
import SymmetricSubgroupAsymptotics.WreathCompressionKernelCongruence

/-! Compress the FULL SOCLE of an actual primitive nonaffine LOCAL component.
The original correlated wreath source pays one genuine simple ordinary rank
per actual minimal normal in the proved one/two-normal cover. Its remaining
chief trace belongs to the SAME source quotient by the literal local socle.
No simple two-generation or numerical aggregate is assumed. -/
set_option autoImplicit false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics.ActualWreathPrimitiveSocleOrdinaryCompression
open PermutationalWreathProduct PrimitiveSocleRawStructure

variable {Q I : Type} [Group Q] [Fintype I] [Nonempty I]
    [MulAction Q I] [FaithfulSMul Q I]
    (S : ActualWreathCompressionState Q I)

private theorem local_minimal_step {T J : Type} [Group T] [Finite T]
    [IsSimpleGroup T] [Fintype J] (E : Subgroup S.D) [E.Normal]
    (eE : E ≃* (J → T)) (j : J) (hE : IsMinimalNormalSubgroup E)
    (hT : IsCenterless T) (hnc : ¬ IsMulCommutative T) :
    MarkedC4.genRank S.A ≤ MarkedC4.genRank T+
      MarkedC4.genRank (S.quotient (S.D ⧸ E) (QuotientGroup.mk' E)
        (QuotientGroup.mk'_surjective E)).A := by
  let phi := QuotientGroup.mk' E
  let e : phi.ker ≃* (J → T) :=
    (MulEquiv.subgroupCongr (QuotientGroup.ker_mk' E)).trans eE
  have hmin : IsMinimalNormalSubgroup phi.ker := by
    rw [QuotientGroup.ker_mk']
    exact hE
  exact ActualWreathIsotypicNonabelianOrdinaryStep.genRank_le_simple_add_next
    S phi e hT j hnc hmin (QuotientGroup.mk'_surjective E)

private theorem two_local_minimals {T J K : Type} [Group T] [Finite T]
    [IsSimpleGroup T] [Fintype J] [Fintype K]
    (E F : Subgroup S.D) [E.Normal] [F.Normal]
    (eE : E ≃* (J → T)) (eF : F ≃* (K → T)) (j : J) (k : K)
    (hE : IsMinimalNormalSubgroup E) (hF : IsMinimalNormalSubgroup F)
    (hdis : Disjoint E F) (hT : IsCenterless T) (hnc : ¬ IsMulCommutative T) :
    MarkedC4.genRank S.A ≤ 2*MarkedC4.genRank T+
      MarkedC4.genRank (S.quotient (S.D ⧸ (E⊔F)) (QuotientGroup.mk' (E⊔F))
        (QuotientGroup.mk'_surjective (E⊔F))).A := by
  let phi := QuotientGroup.mk' E
  let S1 := S.quotient (S.D ⧸ E) phi (QuotientGroup.mk'_surjective E)
  let Fq : Subgroup (S.D ⧸ E) := F.map phi
  let eFq : F ≃* Fq :=
    TwoMinimalNormalIsotypicOrdinaryGenerators.quotientFactorEquiv E F hdis
  letI : Nontrivial F := F.nontrivial_iff_ne_bot.mpr hF.2.1
  letI : Nontrivial Fq := eFq.injective.nontrivial
  have hFqne : Fq ≠ ⊥ := Fq.nontrivial_iff_ne_bot.mp inferInstance
  have hFq := MarkedC4.SocleSurjectiveImage.minimalNormal_map phi
    (QuotientGroup.mk'_surjective E) F hF hFqne
  letI : Fq.Normal := hFq.1
  let psi := QuotientGroup.mk' Fq
  have hfirst := local_minimal_step S E eE j hE hT hnc
  letI : @Subgroup.Normal S1.D S1.groupD Fq := hFq.1
  have hsecond := local_minimal_step S1 Fq (eFq.symm.trans eF) k hFq hT hnc
  change MarkedC4.genRank S.A ≤ MarkedC4.genRank T+MarkedC4.genRank S1.A at hfirst
  change MarkedC4.genRank S1.A ≤ MarkedC4.genRank T+
    MarkedC4.genRank (S1.A ⧸ Compression.kernel S1.rho psi) at hsecond
  have hker : (psi.comp phi).ker = (QuotientGroup.mk' (E⊔F)).ker := by
    rw [← MonoidHom.comap_ker, QuotientGroup.ker_mk', QuotientGroup.ker_mk']
    exact QuotientGroup.comap_map_mk' E F
  have hkernel := WreathCompressionKernelCongruence.kernel_eq_of_ker_eq
    S.rho (psi.comp phi) (QuotientGroup.mk' (E⊔F)) hker
  let eq := (WreathCompressionQuotientComposition.quotientCompositionEquiv
    S.rho phi psi).trans (QuotientGroup.quotientMulEquivOfEq hkernel)
  have hquot : MarkedC4.genRank (S1.A ⧸ Compression.kernel S1.rho psi) =
      MarkedC4.genRank (S.quotient (S.D ⧸ (E⊔F)) (QuotientGroup.mk' (E⊔F))
        (QuotientGroup.mk'_surjective (E⊔F))).A :=
    CoprimeNilpotentProductGenerators.genRank_mulEquiv eq
  rw [hquot] at hsecond
  omega

variable {X : Type} [Finite X] [MulAction S.D X] [FaithfulSMul S.D X]
    [Nontrivial X] [MulAction.IsPreprimitive S.D X]
    (D : NonaffineData S.D X)

/-- The original source quotient obtained by compressing the literal full
socle of its displayed local primitive component. -/
def socleState : ActualWreathCompressionState Q I :=
  S.quotient (S.D ⧸ finiteGroupSocle S.D)
    (QuotientGroup.mk' (finiteGroupSocle S.D))
    (QuotientGroup.mk'_surjective (finiteGroupSocle S.D))

/-- One or two actual local minimal normals pay the whole local socle,
independently of the number of blocks or diagonal source factors. -/
theorem genRank_le_twice_simple_add_socle_quotient :
    MarkedC4.genRank S.A ≤ 2*MarkedC4.genRank D.Simple+
      MarkedC4.genRank (socleState S).A := by
  let N := finiteGroupSocle S.D
  have hT := centerless_of_nonabelian_simple D.Simple D.noncommutative
  obtain ⟨E,hE,_,hcover⟩ :=
    PrimitiveSocleIsotypicOrdinaryCompression.exists_minimal_normal_cover D
  letI : E.Normal := hE.1
  have hEN : E ≤ N := by
    intro x hx
    exact Subgroup.subset_normalClosure ⟨E,hE,hx⟩
  let eE := NormalIsotypicCoordinateOrigins.coordinates N E hEN D.socleEquiv hT
  let j := Classical.choice
    (NormalIsotypicCoordinateOrigins.coordinates_nonempty N E hEN D.socleEquiv hT hE.2.1)
  rcases hcover with hsingle | ⟨F,hF,hdis,hs⟩
  · have hh := local_minimal_step S E eE j hE hT D.noncommutative
    have hker : (QuotientGroup.mk' E).ker = (QuotientGroup.mk' N).ker := by
      rw [QuotientGroup.ker_mk',QuotientGroup.ker_mk']
      exact hsingle.symm
    have hkernel := WreathCompressionKernelCongruence.kernel_eq_of_ker_eq S.rho
      (QuotientGroup.mk' E) (QuotientGroup.mk' N) hker
    have hquot : MarkedC4.genRank
        (S.quotient (S.D ⧸ E) (QuotientGroup.mk' E)
          (QuotientGroup.mk'_surjective E)).A = MarkedC4.genRank (socleState S).A :=
      CoprimeNilpotentProductGenerators.genRank_mulEquiv
        (QuotientGroup.quotientMulEquivOfEq hkernel)
    rw [hquot] at hh
    omega
  · letI : F.Normal := hF.1
    have hFN : F ≤ N := by
      intro x hx
      exact Subgroup.subset_normalClosure ⟨F,hF,hx⟩
    let eF := NormalIsotypicCoordinateOrigins.coordinates N F hFN D.socleEquiv hT
    let k := Classical.choice
      (NormalIsotypicCoordinateOrigins.coordinates_nonempty N F hFN D.socleEquiv hT hF.2.1)
    have hh := two_local_minimals S E F eE eF j k hE hF hdis hT D.noncommutative
    have hker : (QuotientGroup.mk' (E⊔F)).ker = (QuotientGroup.mk' N).ker := by
      rw [QuotientGroup.ker_mk',QuotientGroup.ker_mk']
      exact hs.symm
    have hkernel := WreathCompressionKernelCongruence.kernel_eq_of_ker_eq S.rho
      (QuotientGroup.mk' (E⊔F)) (QuotientGroup.mk' N) hker
    have hquot : MarkedC4.genRank
        (S.quotient (S.D ⧸ (E⊔F)) (QuotientGroup.mk' (E⊔F))
          (QuotientGroup.mk'_surjective (E⊔F))).A = MarkedC4.genRank (socleState S).A :=
      CoprimeNilpotentProductGenerators.genRank_mulEquiv
        (QuotientGroup.quotientMulEquivOfEq hkernel)
    rw [hquot] at hh
    exact hh

omit [FaithfulSMul S.D X] [Nontrivial X] [MulAction.IsPreprimitive S.D X] in
/-- In the one-factor case there is only ONE genuine simple-rank charge. -/
theorem genRank_le_simple_add_socle_quotient_of_one_factor (hk : D.factorCount = 1) :
    MarkedC4.genRank S.A ≤ MarkedC4.genRank D.Simple+
      MarkedC4.genRank (socleState S).A := by
  let N := finiteGroupSocle S.D
  have hmin : IsMinimalNormalSubgroup N := by
    refine ⟨inferInstance,D.oneFactor_socle_nontrivial hk,?_⟩
    intro M hM hMne hMN
    exact le_antisymm hMN (D.oneFactor_socle_le hk M hM hMne)
  exact local_minimal_step S N D.socleEquiv ⟨0,D.factorCount_pos⟩ hmin
    (centerless_of_nonabelian_simple D.Simple D.noncommutative) D.noncommutative

/-- The remaining debt is an actual chief trace of the SAME compressed
source, with the original top retained. No desired scalar inequality is a
constructor or premise. -/
theorem exists_socle_quotient_chiefCost (i : I) :
    ∃ n : ℕ, ActualWreathOrdinaryChiefRecurrence.ChiefCost i (socleState S) n ∧
      MarkedC4.genRank S.A ≤ 2*MarkedC4.genRank D.Simple+n+MarkedC4.genRank Q := by
  obtain ⟨n,hn⟩ := ActualWreathOrdinaryChiefRecurrence.exists_chiefCost i (socleState S)
  have hnext := ActualWreathOrdinaryChiefRecurrence.genRank_le_cost_add_top hn
  have hfirst := genRank_le_twice_simple_add_socle_quotient S D
  exact ⟨n,hn,by omega⟩

theorem exists_generating_finset (i : I) :
    ∃ n : ℕ, ActualWreathOrdinaryChiefRecurrence.ChiefCost i (socleState S) n ∧
      ∃ F : Finset S.A, Subgroup.closure (F : Set S.A) = ⊤ ∧
        F.card ≤ 2*MarkedC4.genRank D.Simple+n+MarkedC4.genRank Q := by
  obtain ⟨n,hn,hbound⟩ := exists_socle_quotient_chiefCost S D i
  obtain ⟨F,hcard,hgen⟩ := MarkedC4.genRank_spec (G := S.A)
  exact ⟨n,hn,F,hgen,hcard.le.trans hbound⟩

end SymmetricSubgroupAsymptotics.ActualWreathPrimitiveSocleOrdinaryCompression
