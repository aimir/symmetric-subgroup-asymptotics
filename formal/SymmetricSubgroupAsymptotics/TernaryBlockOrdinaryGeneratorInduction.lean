import SymmetricSubgroupAsymptotics.TernaryBlockKernelCoordinates
import SymmetricSubgroupAsymptotics.MonomialPolynomialOrbitGenerators
import SymmetricSubgroupAsymptotics.LinearSemidirectUniformNormalGenerators
import SymmetricSubgroupAsymptotics.RepresentationDualSubquotientGenerators
import SymmetricSubgroupAsymptotics.AbelianKernelOrdinaryGeneration
import SymmetricSubgroupAsymptotics.PermutationOrdinarySmallerActions
import SymmetricSubgroupAsymptotics.TransitiveBlockQuotient

/-! All three-point block components satisfy the sharp ordinary-generator
induction. Sign compression gives a genuinely faithful quotient action
on twice the number of blocks. Its kernel is the actual correlated
ternary rotation subspace, with destination-dependent monomial signs.
Only this proved abelian kernel uses ambient normal generators. -/
set_option autoImplicit false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics.TernaryBlockOrdinaryGeneratorInduction
open TernaryBlockKernelCoordinates PermutationOrdinarySmallerActions

variable {G Ω X : Type} [Group G] [Finite G] [Finite Ω] [Finite X]
    [MulAction G Ω] [MulAction G X] [MulAction.IsPretransitive G X]
    [FaithfulSMul G Ω]
    (b : Ω → X) (hb : ∀ (g : G) (ω : Ω), b (g • ω) = g • b ω)
    (x₀ : X) (e : Fin 3 ≃ originalBlockFibre b x₀)

/-- The actual sign quotient acts faithfully on two points per original
block, not on an independently chosen product extension. -/
def quotientAction : G ⧸ evenKernel b hb x₀ e →*
    Equiv.Perm (Multiplicative (ZMod 2) × X) :=
  (PermutationalWreathProduct.toPerm
    (D:=Multiplicative (ZMod 2)) (Q:=Top (G:=G) (X:=X)) (I:=X)
    (Lambda:=Multiplicative (ZMod 2))).comp
      (PermutationalWreathProduct.Compression.quotientEmbedding
        (wreath b hb x₀ e) oddMarkerSign)

omit [Finite G] [Finite Ω] [Finite X] in
theorem quotientAction_injective [Nonempty X] : Function.Injective (quotientAction b hb x₀ e) :=
  (PermutationalWreathProduct.toPerm_injective
    (D:=Multiplicative (ZMod 2)) (Q:=Top (G:=G) (X:=X)) (I:=X)
    (Lambda:=Multiplicative (ZMod 2))).comp
      (PermutationalWreathProduct.Compression.quotientEmbedding_injective
        (wreath b hb x₀ e) oddMarkerSign)

theorem normalGen_evenKernel_le_half [Nontrivial X] :
    MarkedC4.normalGen (evenKernel b hb x₀ e) ≤ Nat.card X / 2 := by
  letI : Fintype X := Fintype.ofFinite X
  have huniform : UniformSubrepresentationGeneratorBound
      (monomialRepresentation b hb x₀ e) (Nat.card X / 2) :=
    MonomialPolynomialOrbitGenerators.uniform_of_transitive
      (monomialRepresentation b hb x₀ e) (monomialRepresentation_single b hb x₀ e)
  have hquot : UniformSubrepresentationGeneratorBound
      (elementaryChart b hb x₀ e).quotientRepresentation.ρ (Nat.card X / 2) := by
    apply UniformSubrepresentationGeneratorBound.of_comp
      (elementaryChart b hb x₀ e).quotientRepresentation.ρ
      (QuotientGroup.mk' (evenKernel b hb x₀ e))
    change UniformSubrepresentationGeneratorBound
      (show Representation (ZMod 3) G (kernelSpace b hb x₀ e) from
        (elementaryChart b hb x₀ e).quotientRepresentation.ρ.comp
          (QuotientGroup.mk' (evenKernel b hb x₀ e))) (Nat.card X / 2)
    exact huniform.of_injective (kernelInclusion b hb x₀ e)
      (kernelSpace b hb x₀ e).subtype_injective
  exact ElementaryUniformNormalGenerators.kernel_normalGen_le
    (evenKernel b hb x₀ e) (elementaryChart b hb x₀ e) (Nat.card X / 2)
    hquot (evenKernel b hb x₀ e) le_rfl

include b hb x₀ e in
/-- Full S3 local components and full S3 top actions are included. The
strictly smaller quotient degree is even, so has no degree-three exception. -/
theorem half_degree_of_ternary_fibres [Nontrivial X]
    (hbelow : SmallerActionBound (Nat.card Ω)) :
    2 * MarkedC4.genRank G ≤ Nat.card Ω := by
  have hfibre : Nat.card (originalBlockFibre b x₀) = 3 := by
    have hh := (Nat.card_congr e).symm
    simpa only [Nat.card_fin] using hh
  have hdegree : Nat.card Ω = 3 * Nat.card X := by
    have hh := Nat.card_congr (ActualBlockWreathEmbedding.productEquiv b hb x₀)
    rw [Nat.card_prod,hfibre] at hh
    exact hh.symm
  let Y := Multiplicative (ZMod 2) × X
  have hbinary : Nat.card (Multiplicative (ZMod 2)) = 2 := by
    rw [Nat.card_congr (Multiplicative.toAdd : Multiplicative (ZMod 2) ≃ ZMod 2),
      Nat.card_zmod]
  have hpoints : Nat.card Y = 2 * Nat.card X := by
    change Nat.card (Multiplicative (ZMod 2) × X) = _
    rw [Nat.card_prod,hbinary]
  have htwo : 2 ≤ Nat.card X := by
    have hh : 1 < Nat.card X := Finite.one_lt_card_iff_nontrivial.mpr inferInstance
    omega
  letI : MulAction (G ⧸ evenKernel b hb x₀ e) Y :=
    MulAction.compHom Y (quotientAction b hb x₀ e)
  letI : FaithfulSMul (G ⧸ evenKernel b hb x₀ e) Y := by
    constructor
    intro u v he
    apply quotientAction_injective b hb x₀ e
    exact Equiv.ext he
  have hQ := hbelow (G ⧸ evenKernel b hb x₀ e) Y (by omega) (by omega)
  letI : IsMulCommutative (evenKernel b hb x₀ e) :=
    evenKernel_isMulCommutative b hb x₀ e
  letI : IsMulCommutative (QuotientGroup.mk' (evenKernel b hb x₀ e)).ker := by
    rw [QuotientGroup.ker_mk']
    infer_instance
  have hG := AbelianKernelOrdinaryGeneration.genRank_le_quotient_add_normalGen
    (QuotientGroup.mk' (evenKernel b hb x₀ e))
    (QuotientGroup.mk'_surjective (evenKernel b hb x₀ e))
  rw [QuotientGroup.ker_mk'] at hG
  have hK := normalGen_evenKernel_le_half b hb x₀ e
  omega

include b hb x₀ e in
theorem exists_half_degree_generators [Nontrivial X]
    (hbelow : SmallerActionBound (Nat.card Ω)) :
    ∃ S : Finset G, Subgroup.closure (S : Set G) = ⊤ ∧ 2 * S.card ≤ Nat.card Ω := by
  obtain ⟨S,hS,hgen⟩ := MarkedC4.genRank_spec (G:=G)
  exact ⟨S,hgen,by rw [hS]; exact half_degree_of_ternary_fibres b hb x₀ e hbelow⟩

/-- Literal original subgroup installer from its actual three-point
stabilizer overgroup. There is no current-degree callback. -/
theorem subgroup_half_degree_generators (n : ℕ) (J : Subgroup (Equiv.Perm (Fin n)))
    (htrans : MulAction.IsPretransitive J (Fin n)) (ω₀ : Fin n) (H : Subgroup J)
    (hH : MulAction.stabilizer J ω₀ ≤ H) (hproper : H < ⊤)
    (hthree : (MulAction.stabilizer J ω₀).relIndex H = 3)
    (hbelow : ∀ (k : ℕ), k < n → ∀ L : Subgroup (Equiv.Perm (Fin k)),
      (k = 3 → L ≠ ⊤) → ∃ S : Finset L, Subgroup.closure (S : Set L) = ⊤ ∧ 2 * S.card ≤ k) :
    ∃ S : Finset J, Subgroup.closure (S : Set J) = ⊤ ∧ 2 * S.card ≤ n := by
  letI : MulAction.IsPretransitive J (Fin n) := htrans
  let b := originalTransitiveBlockMap ω₀ H
  have hb := originalTransitiveBlockMap_equivariant ω₀ H hH
  let x₀ : J ⧸ H := ((1:J):J⧸H)
  have hfibre : Nat.card (originalBlockFibre b x₀) = 3 :=
    (originalTransitiveBlockFibre_card ω₀ H hH).trans hthree
  let e : Fin 3 ≃ originalBlockFibre b x₀ := (Finite.equivFinOfCardEq hfibre).symm
  letI : Nontrivial (J ⧸ H) := Finite.one_lt_card_iff_nontrivial.mp
    (Subgroup.one_lt_index_of_ne_top hproper.ne)
  have hbase : SmallerActionBound (Nat.card (Fin n)) := by
    simpa only [Nat.card_fin] using smallerActionBound_of_subgroup_generators n hbelow
  have hh := exists_half_degree_generators b hb x₀ e hbase
  simpa only [Nat.card_fin] using hh

end SymmetricSubgroupAsymptotics.TernaryBlockOrdinaryGeneratorInduction
