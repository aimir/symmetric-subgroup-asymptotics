import SymmetricSubgroupAsymptotics.CFSGOrthogonalBPointRadicalIndex
import SymmetricSubgroupAsymptotics.NondegenerateBilinearPuncturedAnnihilatorOrbitIndex
import SymmetricSubgroupAsymptotics.OrthogonalBOddScaledClassEnvelope

/-! The literal odd-B point semidirect product retains the SAME kernel
prime-field subspace J and projected subgroup L. Removing the zero
annihilator improves the ternary rank-three motion degree72 to81.
No larger-field invariance, transitivity, or parabolic recognition is assumed. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGOrthogonalBTernaryPuncturedPointIndex
open CFSGOrthogonalBSerreMatrices CFSGOrthogonalBPointRadicalExtension
open CFSGOrthogonalBOddPoleShearElementary CFSGOrthogonalBOddQuadraticForm
open CFSGOrthogonalBPointRadicalNormalizer CFSGOrthogonalBAllNormOrbitCardinality
open CFSGOrthogonalBPointRadicalStabilizerIndex
open CFSGOrthogonalBPointRadicalHom

variable (K : Type) [Field K]
local instance pointPrimeAlgebra (p : ℕ) [Fact p.Prime] [CharP K p] :
    Algebra (ZMod p) K := ZMod.algebra K p

private theorem punctured_natural_slice [Finite K] (h2 : (2:K)≠0)
    (p : ℕ) [Fact p.Prime] [CharP K p] (s : ℕ)
    (M : Subgroup (PointParabolic K s)) (z : Index (s+2) → K)
    (hz : SemidirectProduct.inl (Multiplicative.ofAdd z) ∉ M) :
    (Nat.card K^(s+2)-1)*Nat.card K^(s+2) ≤
      ((M.comap SemidirectProduct.inl).index-1)*(M.map SemidirectProduct.rightHom).index := by
  let J := kernelSubmodule K p s M
  let L := M.map SemidirectProduct.rightHom
  let ρ := naturalLinearHom K (s+2)
  let Q := quadratic K (s+2)
  have hJ : ∀ g ∈ L, ∀ v ∈ J,
      FiniteFieldFunctionalOrbitTransfer.restrictedRepresentation (F := ZMod p) ρ g v ∈ J := by
    intro g hg v hv
    change Multiplicative.ofAdd v ∈ M.comap SemidirectProduct.inl at hv
    change tailAction K s g (Multiplicative.ofAdd v) ∈ M.comap SemidirectProduct.inl
    exact AbelianSemidirectStabilizerIndex.action_mem_kernel_of_projected
      (tailAction K s) M g hg (Multiplicative.ofAdd v) hv
  have hρ : ∀ g : elementaryRootGroup K (s+2), ∀ v w : Index (s+2) → K,
      Q.polarBilin (ρ g v) (ρ g w)=Q.polarBilin v w := by
    intro g v w
    exact QuadraticHyperbolicRadicalHom.polar_preserved Q (ρ g)
      (tail_preserves_quadratic K h2 s g) v w
  have hlow := NondegenerateBilinearPuncturedAnnihilatorOrbitIndex.natural_orbit_lower_le_punctured_quotient_card_mul_index
    Q.polarBilin (quadratic_nondegenerate K h2 (s+2)) ρ hρ
    ((Nat.card K^(s+2)-1)*Nat.card K^(s+2))
    (fun v hv => norm_slice_le_vectorOrbit K h2 s v hv) L J hJ z hz
  rw [quotient_card_eq_kernel_index K p s M] at hlow
  exact hlow

theorem ternary_rank_three_le_index [Finite K] [CharP K 3]
    (hK : Nat.card K=3) (h2 : (2:K)≠0)
    (M : Subgroup (PointParabolic K 0)) (z : Index 2 → K)
    (hz : SemidirectProduct.inl (Multiplicative.ofAdd z) ∉ M) : 81 ≤ M.index := by
  letI : Fact (Nat.Prime 3) := ⟨by decide⟩
  let J := kernelSubmodule K 3 0 M
  let L := M.map SemidirectProduct.rightHom
  have hlow := punctured_natural_slice K h2 3 0 M z hz
  have hc : Nat.card ((Index 2 → K) ⧸ J)=
      3^(Module.finrank (ZMod 3) ((Index 2 → K) ⧸ J)) := by
    simpa only [Nat.card_zmod] using Module.natCard_eq_pow_finrank
      (K := ZMod 3) (V := (Index 2 → K) ⧸ J)
  have hkernel : (M.comap SemidirectProduct.inl).index=
      3^(Module.finrank (ZMod 3) ((Index 2 → K) ⧸ J)) :=
    (quotient_card_eq_kernel_index K 3 0 M).symm.trans hc
  have h72 : 72 ≤ (3^(Module.finrank (ZMod 3) ((Index 2 → K) ⧸ J))-1)*L.index := by
    simpa only [hK,hkernel,Nat.reduceAdd,Nat.reducePow,Nat.reduceSub,Nat.reduceMul] using hlow
  have h81 := OrthogonalBOddScaledClassEnvelope.eightyOne_le_ternary_multiple
    (Module.finrank (ZMod 3) ((Index 2 → K) ⧸ J)) L.index (Nat.pos_of_ne_zero L.index_ne_zero_of_finite) h72
  rw [←hkernel] at h81
  exact h81.trans_eq (AbelianSemidirectStabilizerIndex.index_factor (tailAction K 0) M).symm

theorem ternary_rank_three_degree_bound [Finite K] [CharP K 3]
    (hK : Nat.card K=3) (h2 : (2:K)≠0)
    {X : Type*} [Finite X] [MulAction (PointParabolic K 0) X]
    (x : X) (z : Index 2 → K)
    (hx : (SemidirectProduct.inl (Multiplicative.ofAdd z) : PointParabolic K 0) • x ≠ x) :
    81 ≤ Nat.card X := by
  let M := MulAction.stabilizer (PointParabolic K 0) x
  have hz : (SemidirectProduct.inl (Multiplicative.ofAdd z) : PointParabolic K 0) ∉ M := hx
  have hb := ternary_rank_three_le_index K hK h2 M z hz
  have ho : M.index=Nat.card (MulAction.orbit (PointParabolic K 0) x) :=
    (Nat.card_congr (MulAction.orbitEquivQuotientStabilizer (PointParabolic K 0) x)).symm
  rw [ho] at hb
  exact hb.trans (Nat.card_le_card_of_injective
    (fun y : MulAction.orbit (PointParabolic K 0) x => y.val) Subtype.val_injective)

theorem projective_ternary_rank_three_le_proper_index [Finite K] [CharP K 3]
    (hK : Nat.card K=3) (h2 : (2:K)≠0)
    [IsSimpleGroup (elementaryProjective K 3)]
    (H : Subgroup (elementaryProjective K 3)) (hH : H≠⊤) : 81 ≤ H.index := by
  letI : Finite (elementaryProjective K 3) :=
    Finite.of_surjective (QuotientGroup.mk' (Subgroup.center (elementaryRootGroup K 3)))
      (QuotientGroup.mk'_surjective _)
  let z : Index 2 → K := Pi.single (pos 2 0) 1
  have hz : z≠0 := by
    intro he
    have hh := congrFun he (pos 2 0)
    exact one_ne_zero (by simpa only [z,Pi.single_eq_same,Pi.zero_apply] using hh)
  let u : Multiplicative (Index 2 → K) := Multiplicative.ofAdd z
  have hu : u≠1 := fun he => hz (congrArg Multiplicative.toAdd he)
  have hn : projectiveExtensionHom K 0 h2 (SemidirectProduct.inl u)≠1 := by
    rw [projectiveExtensionHom_inl]
    intro he
    apply hu
    apply projectiveRadicalHom_injective K h2 0
    exact he.trans (projectiveRadicalHom K h2 0).map_one.symm
  obtain ⟨x,hx⟩ := CFSGConjugateSubgroupDegree.exists_moved_coset_of_ne_one H hH _ hn
  letI : MulAction (PointParabolic K 0) (elementaryProjective K 3 ⧸ H) :=
    MulAction.compHom _ (projectiveExtensionHom K 0 h2)
  have hb := ternary_rank_three_degree_bound K hK h2 x z hx
  simpa only [Subgroup.index_eq_card] using hb

end SymmetricSubgroupAsymptotics.CFSGOrthogonalBTernaryPuncturedPointIndex

namespace SymmetricSubgroupAsymptotics.CFSGReduction
open CFSGOrthogonalBSerreMatrices

theorem typeB_rank_three_three_field_le_proper_index (q : CFSG.PrimePower) (hq : q.order=3)
    [IsSimpleGroup (CFSG.Models.B 3 q)]
    (H : Subgroup (CFSG.Models.B 3 q)) (hH : H≠⊤) : 81 ≤ H.index := by
  have hp : q.prime=3 :=
    (Nat.Prime.pow_inj' q.prime_isPrime (by decide : Nat.Prime 3)
      q.exponent_pos.ne' (by decide : (1:ℕ)≠0)
      (show q.prime^q.exponent=3^1 from hq)).1
  letI : CharP q.Field 3 := by rw [←hp]; infer_instance
  have h2 : (2:q.Field)≠0 :=
    CharP.cast_ne_zero_of_ne_of_prime (R := q.Field) (p := 3) Nat.prime_two (by decide)
  let e : CFSG.Models.B 3 q ≃* elementaryProjective q.Field 3 :=
    serreProjectiveEquivElementaryProjective q.Field 2 h2
  letI : IsSimpleGroup (elementaryProjective q.Field 3) := e.symm.isSimpleGroup
  have hmap : H.map e.toMonoidHom≠⊤ := by
    intro ht
    apply hH
    apply Subgroup.map_injective (f := e.toMonoidHom) e.injective
    exact ht.trans (Subgroup.map_top_of_surjective e.toMonoidHom e.surjective).symm
  have hb := CFSGOrthogonalBTernaryPuncturedPointIndex.projective_ternary_rank_three_le_proper_index
    q.Field (q.card_field.trans hq) h2 (H.map e.toMonoidHom) hmap
  exact hb.trans_eq (H.index_map_equiv e)

end SymmetricSubgroupAsymptotics.CFSGReduction
