import SymmetricSubgroupAsymptotics.ActualWreathOrdinaryChiefRecurrence
import SymmetricSubgroupAsymptotics.MinimalNormalIsotypicRelativeOrdinaryGenerators

/-! A local isotypic nonabelian minimal normal costs ONE genuine simple
ordinary rank in the actual correlated wreath source, independent of the
number of blocks and diagonal kernel factors. The original coordinate
origins, actual quotient state and supported factor marking are retained.
No direct-product independence or simple two-generation is inferred. -/
set_option autoImplicit false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics.ActualWreathIsotypicNonabelianOrdinaryStep
open PermutationalWreathProduct

variable {Q I T J : Type} [Group Q] [Fintype I] [Nonempty I]
    [MulAction Q I] [FaithfulSMul Q I] [Group T] [Finite T] [IsSimpleGroup T] [Fintype J]
    (S : ActualWreathCompressionState Q I)
    {D' : Type} [Group D'] [Finite D'] (phi : S.D →* D')
    (e : phi.ker ≃* (J → T)) (hT : IsCenterless T)

def localChart : SemisimpleNormalChart phi.ker where
  ι := J
  factor := fun _ => T
  simple := fun _ => inferInstance
  centerless := fun _ => hT
  equiv := e

def kernelOrigins : SemisimpleGroupChartOrigins (Compression.kernel S.rho phi)
    (I × J) (fun _ => T) :=
  Compression.kernelSemisimpleChartOriginsOfFullComponent S.rho phi
    S.rho_injective S.fullComponent (localChart S phi e hT)

def kernelCoordinates : Compression.kernel S.rho phi ≃*
    ((kernelOrigins S phi e hT).ι → T) :=
  (kernelOrigins S phi e hT).equiv.trans
    (MulEquiv.piCongrRight (kernelOrigins S phi e hT).factor_equiv)

theorem kernelCoordinates_nonempty (hne : Compression.kernel S.rho phi ≠ ⊥) :
    Nonempty (kernelOrigins S phi e hT).ι := by
  let K := Compression.kernel S.rho phi
  letI : Nontrivial K := K.nontrivial_iff_ne_bot.mpr hne
  obtain ⟨x,hx⟩ := exists_ne (1 : K)
  by_contra hn
  apply hx
  apply (kernelCoordinates S phi e hT).injective
  funext j
  exact False.elim (hn ⟨j⟩)

include e in
private theorem local_noncommutative (j : J) (hnc : ¬ IsMulCommutative T) :
    ¬ IsMulCommutative phi.ker := by
  intro hA
  apply hnc
  apply isMulCommutative_iff.mpr
  intro x y
  have hh := congrArg (fun z : phi.ker => e z j)
    (isMulCommutative_iff.mp hA
      (e.symm (Pi.mulSingle j x)) (e.symm (Pi.mulSingle j y)))
  simpa only [map_mul,Pi.mul_apply,MulEquiv.apply_symm_apply,Pi.mulSingle_eq_same] using hh

include e hT in
theorem genRank_le_simple_add_next (j : J) (hnc : ¬ IsMulCommutative T)
    (hmin : IsMinimalNormalSubgroup phi.ker) (hphi : Function.Surjective phi) :
    MarkedC4.genRank S.A ≤ MarkedC4.genRank T+MarkedC4.genRank (S.quotient D' phi hphi).A := by
  let K := Compression.kernel S.rho phi
  change MarkedC4.genRank S.A ≤ MarkedC4.genRank T+MarkedC4.genRank (S.A ⧸ K)
  by_cases hz : K = ⊥
  · let f : S.A →* S.A ⧸ K := QuotientGroup.mk' K
    have hf : Function.Injective f := (MonoidHom.ker_eq_bot_iff f).mp
      ((QuotientGroup.ker_mk' K).trans hz)
    let eA := MulEquiv.ofBijective f ⟨hf,QuotientGroup.mk'_surjective K⟩
    have hh := CoprimeNilpotentProductGenerators.genRank_mulEquiv eA
    omega
  · letI : MulAction.IsPretransitive Q I := S.top_pretransitive
    have hminK := WreathNonabelianChiefOrdinaryStep.minimalNormal_kernel S.rho phi
      S.rho_injective S.top_surjective S.fullComponent hmin
      (local_noncommutative S phi e j hnc) hz
    let k := Classical.choice (kernelCoordinates_nonempty S phi e hT hz)
    exact MinimalNormalIsotypicRelativeOrdinaryGenerators.genRank_le K
      (kernelCoordinates S phi e hT) k hminK

include e hT in
theorem exists_generating_finset (j : J) (hnc : ¬ IsMulCommutative T)
    (hmin : IsMinimalNormalSubgroup phi.ker) (hphi : Function.Surjective phi) :
    ∃ s : Finset S.A, Subgroup.closure (s : Set S.A) = ⊤ ∧
      s.card ≤ MarkedC4.genRank T+MarkedC4.genRank (S.quotient D' phi hphi).A := by
  obtain ⟨s,hs,hgen⟩ := MarkedC4.genRank_spec (G := S.A)
  exact ⟨s,hgen,hs.le.trans (genRank_le_simple_add_next S phi e hT j hnc hmin hphi)⟩

end SymmetricSubgroupAsymptotics.ActualWreathIsotypicNonabelianOrdinaryStep
