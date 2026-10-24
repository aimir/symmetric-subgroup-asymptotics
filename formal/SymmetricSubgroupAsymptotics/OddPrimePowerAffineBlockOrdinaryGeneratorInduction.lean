import SymmetricSubgroupAsymptotics.OddPrimePowerAffineBlockPairCompression
import SymmetricSubgroupAsymptotics.OddAffineBlockGeneratorNumerics
import SymmetricSubgroupAsymptotics.BlockMonomialPolynomialOrbitGenerators
import SymmetricSubgroupAsymptotics.PrimitiveAffineOddOrdinaryInduction
import SymmetricSubgroupAsymptotics.AbelianKernelOrdinaryGeneration
import SymmetricSubgroupAsymptotics.RepresentationDualSubquotientGenerators
import SymmetricSubgroupAsymptotics.LinearSemidirectUniformNormalGenerators
import SymmetricSubgroupAsymptotics.OriginalMinimalBlock

/-! All odd-prime-power affine block components of degree at least five
satisfy sharp ordinary-generator induction. Both kernels are the actual
correlated normal subgroups; only their proved abelianity permits use of
ambient normal generators. The smaller quotient uses inverse pairs and
retains its rounded S3 exception. No same-degree callback occurs. -/
set_option autoImplicit false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics.OddPrimePowerAffineBlockOrdinaryGeneratorInduction
open OddPrimePowerAffineBlockCoordinates OddPrimePowerAffineBlockPairCompression
open PermutationOrdinarySmallerActions

variable {G Ω X : Type} [Group G] [Finite G] [Finite Ω] [Finite X]
    [MulAction G Ω] [MulAction G X] [MulAction.IsPretransitive G X]
    [FaithfulSMul G Ω]
    (b : Ω → X) (hb : ∀ (g : G) (ω : Ω), b (g • ω) = g • b ω)
    (x₀ : X) [Nontrivial (originalBlockFibre b x₀)]
    (P : PrimitiveAffineProfile (Component b hb x₀) (originalBlockFibre b x₀))
    (hprimitive : MulAction.IsPreprimitive (Component b hb x₀) (originalBlockFibre b x₀))
    (C : P.ElementaryChart hprimitive) (origin : originalBlockFibre b x₀)

include hprimitive C origin in
theorem normalGen_translationKernel_le_half [Nontrivial X] :
    MarkedC4.normalGen (translationKernel b hb x₀ P origin) ≤ C.d*(Nat.card X/2) := by
  letI : Fact P.p.Prime := C.primeFact
  letI : Fintype X := Fintype.ofFinite X
  have huniform : UniformSubrepresentationGeneratorBound
      (blockRepresentation b hb x₀ P hprimitive C) (C.d*(Nat.card X/2)) := by
    simpa only [PrimitiveAffineProfile.ElementaryChart.d] using
      BlockMonomialPolynomialOrbitGenerators.uniform_of_transitive
        (blockRepresentation b hb x₀ P hprimitive C)
        (blockRepresentation_single b hb x₀ P hprimitive C)
  have hquot : UniformSubrepresentationGeneratorBound
      (elementaryChart b hb x₀ P hprimitive C origin).quotientRepresentation.ρ
      (C.d*(Nat.card X/2)) := by
    apply UniformSubrepresentationGeneratorBound.of_comp
      (elementaryChart b hb x₀ P hprimitive C origin).quotientRepresentation.ρ
      (QuotientGroup.mk' (translationKernel b hb x₀ P origin))
    change UniformSubrepresentationGeneratorBound
      (show Representation (ZMod P.p) G (kernelSpace b hb x₀ P hprimitive C origin) from
        (elementaryChart b hb x₀ P hprimitive C origin).quotientRepresentation.ρ.comp
          (QuotientGroup.mk' (translationKernel b hb x₀ P origin))) (C.d*(Nat.card X/2))
    exact huniform.of_injective (kernelInclusion b hb x₀ P hprimitive C origin)
      (kernelSpace b hb x₀ P hprimitive C origin).subtype_injective
  exact ElementaryUniformNormalGenerators.kernel_normalGen_le
    (translationKernel b hb x₀ P origin) (elementaryChart b hb x₀ P hprimitive C origin)
    (C.d*(Nat.card X/2)) hquot (translationKernel b hb x₀ P origin) le_rfl

include hprimitive C origin in
theorem half_degree_of_odd_affine_fibres [Nontrivial X]
    (hp : P.p ≠ 2) (hfive : 5 ≤ Nat.card (originalBlockFibre b x₀))
    (hbelow : SmallerActionBound (Nat.card Ω)) :
    2*MarkedC4.genRank G ≤ Nat.card Ω := by
  letI : Fact P.p.Prime := C.primeFact
  letI : Finite C.V := Finite.of_equiv P.V
    (C.equiv.toEquiv.trans (Multiplicative.toAdd : Multiplicative C.V ≃ C.V))
  let q := Nat.card (originalBlockFibre b x₀)
  let t := Nat.card X
  have ht : 2 ≤ t := by
    have hh := Finite.one_lt_card_iff_nontrivial.mpr (inferInstance : Nontrivial X)
    omega
  have hdegree : Nat.card Ω = q*t := by
    have hh := Nat.card_congr (ActualBlockWreathEmbedding.productEquiv b hb x₀)
    rw [Nat.card_prod] at hh
    exact hh.symm
  have hq : q = P.p^C.d := by
    simpa only [PrimitiveAffineProfile.ElementaryChart.d] using
      P.degree_eq_prime_pow_finrank C.equiv origin
  have hd : 1 ≤ C.d := C.d_pos
  have hp3 : 3 ≤ P.p := P.p_prime.odd_iff.mp (P.p_prime.odd_of_ne_two hp)
  have hdim : 2*C.d+2 ≤ q := by
    rw [hq]
    exact OddAffineBlockGeneratorNumerics.two_mul_add_two_le_pow P.p C.d hp3 hd
      (hq ▸ hfive)
  have hfree : ∀ v : Multiplicative C.V, v ≠ 1 → v⁻¹ ≠ v := by
    intro v hv he
    have hnv : C.equiv.symm v ≠ 1 := by
      intro h
      apply hv
      simpa only [C.equiv.apply_symm_apply,map_one] using congrArg C.equiv h
    have he' : (C.equiv.symm v)⁻¹ = C.equiv.symm v :=
      (map_inv C.equiv.symm v).symm.trans (congrArg C.equiv.symm he)
    exact PrimitiveAffineOddOrdinaryInduction.translation_inverse_ne_self P hp _ hnv he'
  have hcard : Nat.card (Multiplicative C.V) = q :=
    (Nat.card_congr C.equiv).symm.trans (P.card_eq origin)
  have hpairs : 2*Nat.card (Pairs b hb x₀ P hprimitive C) ≤ q-1 := by
    have hh := AbelianAutomorphismInversionPairs.two_mul_pairCard_le (V:=Multiplicative C.V) hfree
    simpa only [hcard] using hh
  obtain ⟨v,hv⟩ := exists_ne (1 : Multiplicative C.V)
  letI : Nonempty (Pairs b hb x₀ P hprimitive C) :=
    ⟨FreeInvolutionPairQuotient.mk
      (AbelianAutomorphismInversionPairs.inversion (Multiplicative C.V))
      (AbelianAutomorphismInversionPairs.inversion_involutive (Multiplicative C.V)) ⟨v,hv⟩⟩
  let E := pairKernel b hb x₀ P hprimitive C origin
  let Y := Pairs b hb x₀ P hprimitive C × X
  have hpoints : 2*Nat.card Y ≤ (q-1)*t := by
    change 2*Nat.card (Pairs b hb x₀ P hprimitive C × X) ≤ (q-1)*t
    rw [Nat.card_prod]
    simpa only [Nat.mul_assoc] using Nat.mul_le_mul_right t hpairs
  have hsum : (q-1)*t+t = q*t := by
    calc
      (q-1)*t+t = ((q-1)+1)*t := by ring
      _ = q*t := by rw [Nat.sub_add_cancel (by omega)]
  have hlt : Nat.card Y < Nat.card Ω := by omega
  letI : MulAction (LinearQuotient b hb x₀ P origin ⧸ E) Y :=
    MulAction.compHom Y (quotientAction b hb x₀ P hprimitive C origin)
  letI : FaithfulSMul (LinearQuotient b hb x₀ P origin ⧸ E) Y := by
    constructor
    intro u v he
    apply quotientAction_injective b hb x₀ P hprimitive C origin
    exact Equiv.ext he
  have htop := rounded_rank_of_smaller (Nat.card Ω) hbelow
    (LinearQuotient b hb x₀ P origin ⧸ E) Y hlt
  letI : IsMulCommutative (translationKernel b hb x₀ P origin) :=
    translationKernel_isMulCommutative b hb x₀ P hprimitive C origin
  letI : IsMulCommutative (QuotientGroup.mk' (translationKernel b hb x₀ P origin)).ker := by
    rw [QuotientGroup.ker_mk']
    infer_instance
  have hG := AbelianKernelOrdinaryGeneration.genRank_le_quotient_add_normalGen
    (QuotientGroup.mk' (translationKernel b hb x₀ P origin))
    (QuotientGroup.mk'_surjective (translationKernel b hb x₀ P origin))
  rw [QuotientGroup.ker_mk'] at hG
  letI : IsMulCommutative E := pairKernel_isMulCommutative b hb x₀ P hprimitive C origin
  letI : IsMulCommutative (QuotientGroup.mk' E).ker := by
    rw [QuotientGroup.ker_mk']
    infer_instance
  have hQ := AbelianKernelOrdinaryGeneration.genRank_le_quotient_add_normalGen
    (QuotientGroup.mk' E) (QuotientGroup.mk'_surjective E)
  rw [QuotientGroup.ker_mk'] at hQ
  have hsign := normalGen_pairKernel_le_half b hb x₀ P hprimitive C origin
  have htranslation := normalGen_translationKernel_le_half b hb x₀ P hprimitive C origin
  have hgen : MarkedC4.genRank G ≤
      MarkedC4.genRank (LinearQuotient b hb x₀ P origin ⧸ E) +
        MarkedC4.normalGen E + MarkedC4.normalGen (translationKernel b hb x₀ P origin) :=
    hG.trans (Nat.add_le_add_right hQ _)
  rw [hdegree]
  exact OddAffineBlockGeneratorNumerics.half_degree_of_three_layers
    q C.d t (MarkedC4.genRank G)
    (MarkedC4.genRank (LinearQuotient b hb x₀ P origin ⧸ E))
    (MarkedC4.normalGen E) (MarkedC4.normalGen (translationKernel b hb x₀ P origin))
    (Nat.card Y) hdim ht hpoints htop hsign htranslation hgen

include hprimitive C origin in
theorem exists_half_degree_generators [Nontrivial X]
    (hp : P.p ≠ 2) (hfive : 5 ≤ Nat.card (originalBlockFibre b x₀))
    (hbelow : SmallerActionBound (Nat.card Ω)) :
    ∃ S : Finset G, Subgroup.closure (S : Set G) = ⊤ ∧ 2*S.card ≤ Nat.card Ω := by
  obtain ⟨S,hS,hgen⟩ := MarkedC4.genRank_spec (G:=G)
  exact ⟨S,hgen,by rw [hS]; exact
    half_degree_of_odd_affine_fibres b hb x₀ P hprimitive C origin hp hfive hbelow⟩

/-- The actual cover supplies the primitive local component; its
prime-field chart is chosen inside the proof. Only smaller-degree
permutation sections are used for ordinary generation. -/
theorem subgroup_half_degree_generators (n : ℕ) (J : Subgroup (Equiv.Perm (Fin n)))
    [MulAction.IsPretransitive J (Fin n)] (ω₀ : Fin n)
    (D : OriginalMinimalBlock (A:=J) ω₀)
    (P : PrimitiveAffineProfile D.Component D.Fibre)
    (hp : P.p ≠ 2) (hfive : 5 ≤ Nat.card D.Fibre)
    (hbelow : ∀ (k : ℕ), k < n → ∀ L : Subgroup (Equiv.Perm (Fin k)),
      (k = 3 → L ≠ ⊤) → ∃ S : Finset L, Subgroup.closure (S : Set L) = ⊤ ∧ 2*S.card ≤ k) :
    ∃ S : Finset J, Subgroup.closure (S : Set J) = ⊤ ∧ 2*S.card ≤ n := by
  letI : Nontrivial D.Fibre := Finite.one_lt_card_iff_nontrivial.mp (by omega)
  letI : Nontrivial D.Points := Finite.one_lt_card_iff_nontrivial.mp (by
    have hh := D.degrees_ge_two.2
    omega)
  let C := P.elementaryChart D.component_preprimitive
  let origin : D.Fibre := ⟨ω₀,D.map_base⟩
  have hbase : PermutationOrdinarySmallerActions.SmallerActionBound (Nat.card (Fin n)) := by
    simpa only [Nat.card_fin] using
      PermutationOrdinarySmallerActions.smallerActionBound_of_subgroup_generators n hbelow
  have hh := OddPrimePowerAffineBlockOrdinaryGeneratorInduction.exists_half_degree_generators
    D.map D.map_equivariant D.base P D.component_preprimitive C origin hp hfive hbase
  simpa only [Nat.card_fin] using hh


end SymmetricSubgroupAsymptotics.OddPrimePowerAffineBlockOrdinaryGeneratorInduction
