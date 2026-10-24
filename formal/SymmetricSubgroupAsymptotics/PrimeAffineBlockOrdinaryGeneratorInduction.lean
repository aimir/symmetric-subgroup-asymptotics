import SymmetricSubgroupAsymptotics.PrimeAffineBlockKernelCoordinates
import SymmetricSubgroupAsymptotics.MonomialPolynomialOrbitGenerators
import SymmetricSubgroupAsymptotics.LinearSemidirectUniformNormalGenerators
import SymmetricSubgroupAsymptotics.RepresentationDualSubquotientGenerators
import SymmetricSubgroupAsymptotics.AbelianKernelOrdinaryGeneration
import SymmetricSubgroupAsymptotics.PermutationOrdinarySmallerActions
import SymmetricSubgroupAsymptotics.TransitiveBlockQuotient

/-! Prime-affine blocks satisfy the sharp ordinary-generator induction.
The actual affine component is compressed by its scalar projection, giving
a faithful quotient action on (p-1) points per block. The correlated
additive prime-field kernel needs at most half the number of blocks as
ambient normal generators. Only this proved abelian kernel uses the
ordinary extension bound. -/
set_option autoImplicit false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics.PrimeAffineBlockOrdinaryGeneratorInduction
open PrimeAffineBlockKernelCoordinates PermutationOrdinarySmallerActions

variable (p : ℕ) [Fact p.Prime]

variable {G Ω X : Type} [Group G] [Finite G] [Finite Ω] [Finite X]
    [MulAction G Ω] [MulAction G X] [MulAction.IsPretransitive G X]
    [FaithfulSMul G Ω]
    (b : Ω → X) (hb : ∀ (g : G) (ω : Ω), b (g • ω) = g • b ω)
    (x₀ : X) (C : ComponentCoordinates p b hb x₀)

/-- The actual scalar quotient acts faithfully on p-1 points per original
block, not on an independently chosen product extension. -/
def quotientAction : G ⧸ translationKernel p b hb x₀ C →*
    Equiv.Perm ((ZMod p)ˣ × X) :=
  (PermutationalWreathProduct.toPerm
    (D:=(ZMod p)ˣ) (Q:=Top (G:=G) (X:=X)) (I:=X)
    (Lambda:=(ZMod p)ˣ)).comp
      (PermutationalWreathProduct.Compression.quotientEmbedding
        (wreath p b hb x₀ C) (ScalarAffineLineGroup.scalar (ZMod p)))

omit [Finite G] [Finite Ω] [Finite X] in
theorem quotientAction_injective [Nonempty X] : Function.Injective (quotientAction p b hb x₀ C) :=
  (PermutationalWreathProduct.toPerm_injective
    (D:=(ZMod p)ˣ) (Q:=Top (G:=G) (X:=X)) (I:=X)
    (Lambda:=(ZMod p)ˣ)).comp
      (PermutationalWreathProduct.Compression.quotientEmbedding_injective
        (wreath p b hb x₀ C) (ScalarAffineLineGroup.scalar (ZMod p)))

theorem normalGen_translationKernel_le_half [Nontrivial X] :
    MarkedC4.normalGen (translationKernel p b hb x₀ C) ≤ Nat.card X / 2 := by
  letI : Fintype X := Fintype.ofFinite X
  have huniform : UniformSubrepresentationGeneratorBound
      (monomialRepresentation p b hb x₀ C) (Nat.card X / 2) :=
    MonomialPolynomialOrbitGenerators.uniform_of_transitive
      (monomialRepresentation p b hb x₀ C) (monomialRepresentation_single p b hb x₀ C)
  have hquot : UniformSubrepresentationGeneratorBound
      (elementaryChart p b hb x₀ C).quotientRepresentation.ρ (Nat.card X / 2) := by
    apply UniformSubrepresentationGeneratorBound.of_comp
      (elementaryChart p b hb x₀ C).quotientRepresentation.ρ
      (QuotientGroup.mk' (translationKernel p b hb x₀ C))
    change UniformSubrepresentationGeneratorBound
      (show Representation (ZMod p) G (kernelSpace p b hb x₀ C) from
        (elementaryChart p b hb x₀ C).quotientRepresentation.ρ.comp
          (QuotientGroup.mk' (translationKernel p b hb x₀ C))) (Nat.card X / 2)
    exact huniform.of_injective (kernelInclusion p b hb x₀ C)
      (kernelSpace p b hb x₀ C).subtype_injective
  exact ElementaryUniformNormalGenerators.kernel_normalGen_le
    (translationKernel p b hb x₀ C) (elementaryChart p b hb x₀ C) (Nat.card X / 2)
    hquot (translationKernel p b hb x₀ C) le_rfl

include b hb x₀ C in
/-- Every odd prime and every top action are included. The smaller scalar
quotient has even degree, so the exceptional S3 input is never requested. -/
theorem half_degree_of_affine_prime_fibres [Nontrivial X]
    (hp : 3 ≤ p) (hfibre : Nat.card (originalBlockFibre b x₀) = p)
    (hbelow : SmallerActionBound (Nat.card Ω)) :
    2 * MarkedC4.genRank G ≤ Nat.card Ω := by
  have hdegree : Nat.card Ω = p * Nat.card X := by
    have hh := Nat.card_congr (ActualBlockWreathEmbedding.productEquiv b hb x₀)
    rw [Nat.card_prod,hfibre] at hh
    exact hh.symm
  let Y := (ZMod p)ˣ × X
  have hpoints : Nat.card Y = (p-1) * Nat.card X := by
    change Nat.card ((ZMod p)ˣ × X) = _
    rw [Nat.card_prod,Nat.card_units,Nat.card_zmod]
  have hlt : Nat.card Y < Nat.card Ω := by
    rw [hpoints,hdegree]
    exact Nat.mul_lt_mul_of_pos_right (by omega) Nat.card_pos
  have hne : Nat.card Y ≠ 3 := by
    obtain ⟨a,ha⟩ := (Fact.out : Nat.Prime p).even_sub_one (by omega)
    intro he
    have hparity : Even (Nat.card Y) := ⟨a * Nat.card X,by rw [hpoints,ha]; ring⟩
    rw [he] at hparity
    norm_num at hparity
  letI : MulAction (G ⧸ translationKernel p b hb x₀ C) Y :=
    MulAction.compHom Y (quotientAction p b hb x₀ C)
  letI : FaithfulSMul (G ⧸ translationKernel p b hb x₀ C) Y := by
    constructor
    intro u v he
    apply quotientAction_injective p b hb x₀ C
    exact Equiv.ext he
  have hQ := hbelow (G ⧸ translationKernel p b hb x₀ C) Y hlt hne
  letI : IsMulCommutative (translationKernel p b hb x₀ C) :=
    translationKernel_isMulCommutative p b hb x₀ C
  letI : IsMulCommutative (QuotientGroup.mk' (translationKernel p b hb x₀ C)).ker := by
    rw [QuotientGroup.ker_mk']
    infer_instance
  have hG := AbelianKernelOrdinaryGeneration.genRank_le_quotient_add_normalGen
    (QuotientGroup.mk' (translationKernel p b hb x₀ C))
    (QuotientGroup.mk'_surjective (translationKernel p b hb x₀ C))
  rw [QuotientGroup.ker_mk'] at hG
  have hK := normalGen_translationKernel_le_half p b hb x₀ C
  have hround : 2 * (Nat.card X / 2) ≤ Nat.card X := Nat.mul_div_le _ _
  have hsum : (p-1) * Nat.card X + Nat.card X = p * Nat.card X := by
    calc
      (p-1) * Nat.card X + Nat.card X = ((p-1)+1) * Nat.card X := by ring
      _ = p * Nat.card X := by rw [Nat.sub_add_cancel (by omega)]
  rw [hpoints] at hQ
  omega

include b hb x₀ C in
theorem exists_half_degree_generators [Nontrivial X]
    (hp : 3 ≤ p) (hfibre : Nat.card (originalBlockFibre b x₀) = p)
    (hbelow : SmallerActionBound (Nat.card Ω)) :
    ∃ S : Finset G, Subgroup.closure (S : Set G) = ⊤ ∧ 2 * S.card ≤ Nat.card Ω := by
  obtain ⟨S,hS,hgen⟩ := MarkedC4.genRank_spec (G:=G)
  exact ⟨S,hgen,by rw [hS]; exact
    half_degree_of_affine_prime_fibres p b hb x₀ C hp hfibre hbelow⟩

/-- Literal original-subgroup installer. The local affine profile belongs
to the actual block component and only strictly smaller permutation
sections are used as induction hypotheses. -/
theorem subgroup_half_degree_generators (n : ℕ) (J : Subgroup (Equiv.Perm (Fin n)))
    (htrans : MulAction.IsPretransitive J (Fin n)) (ω₀ : Fin n) (H : Subgroup J)
    (hH : MulAction.stabilizer J ω₀ ≤ H) (hproper : H < ⊤)
    (hprime : Nat.Prime ((MulAction.stabilizer J ω₀).relIndex H))
    (hodd : 3 ≤ (MulAction.stabilizer J ω₀).relIndex H)
    (P : letI : MulAction.IsPretransitive J (Fin n) := htrans
      PrimitiveAffineProfile
      (originalBlockComponent (originalTransitiveBlockMap ω₀ H)
        (originalTransitiveBlockMap_equivariant ω₀ H hH) ((1:J):J⧸H))
      (originalBlockFibre (originalTransitiveBlockMap ω₀ H) ((1:J):J⧸H)))
    (hbelow : ∀ (k : ℕ), k < n → ∀ L : Subgroup (Equiv.Perm (Fin k)),
      (k = 3 → L ≠ ⊤) → ∃ S : Finset L, Subgroup.closure (S : Set L) = ⊤ ∧ 2 * S.card ≤ k) :
    ∃ S : Finset J, Subgroup.closure (S : Set J) = ⊤ ∧ 2 * S.card ≤ n := by
  letI : MulAction.IsPretransitive J (Fin n) := htrans
  let q := (MulAction.stabilizer J ω₀).relIndex H
  letI : Fact q.Prime := ⟨hprime⟩
  let b := originalTransitiveBlockMap ω₀ H
  have hb := originalTransitiveBlockMap_equivariant ω₀ H hH
  let x₀ : J ⧸ H := ((1:J):J⧸H)
  have hfibre : Nat.card (originalBlockFibre b x₀) = q :=
    originalTransitiveBlockFibre_card ω₀ H hH
  let origin : originalBlockFibre b x₀ := ⟨ω₀,originalTransitiveBlockMap_base ω₀ H hH⟩
  let C : ComponentCoordinates q b hb x₀ :=
    componentCoordinatesOfProfile q b hb x₀ P origin hfibre
  letI : Nontrivial (J ⧸ H) := Finite.one_lt_card_iff_nontrivial.mp
    (Subgroup.one_lt_index_of_ne_top hproper.ne)
  have hbase : SmallerActionBound (Nat.card (Fin n)) := by
    simpa only [Nat.card_fin] using smallerActionBound_of_subgroup_generators n hbelow
  have hh := exists_half_degree_generators q b hb x₀ C hodd hfibre hbase
  simpa only [Nat.card_fin] using hh

end SymmetricSubgroupAsymptotics.PrimeAffineBlockOrdinaryGeneratorInduction
