import SymmetricSubgroupAsymptotics.SubnormalCoordinateOrdinaryGenerators
import SymmetricSubgroupAsymptotics.BlockLocalOrderOrdinaryGeneratorInduction

/-! The actual block kernel is bounded using ordinary ranks of
subnormal subgroups of its literal component. Fullness of the original
wreath embedding proves normality of each original coordinate image;
the subsequent kernel filtration retains all coordinate correlations.
No numerical budget for a small component is asserted here. -/
set_option autoImplicit false
noncomputable section
open scoped Classical BigOperators
namespace SymmetricSubgroupAsymptotics.BlockSubnormalOrdinaryGeneratorInduction
open OriginalBlockClassBound PermutationOrdinarySmallerActions
open BlockLocalOrderOrdinaryGeneratorInduction (kernelCoordinate kernelCoordinates_injective)

variable {G Ω X : Type} [Group G] [Finite G] [Finite Ω] [Finite X]
    [MulAction G Ω] [MulAction G X] [MulAction.IsPretransitive G X]
    [FaithfulSMul G Ω]
    (b : Ω → X) (hb : ∀ (g : G) (ω : Ω), b (g • ω) = g • b ω) (x₀ : X)

private theorem kernel_le_wreath_top_kernel :
    Kernel (A := G) (X := X) ≤
      (PermutationalWreathProduct.rightHom.comp
        (ActualBlockWreathEmbedding.embedding b hb x₀)).ker := by
  intro g hg
  change (MulAction.toPermHom G X).rangeRestrict g = 1
  exact Subtype.ext hg

/-- Actual component fullness and original conjugation make the
original coordinate image normal in that same component. -/
theorem kernelCoordinate_range_normal (x : X) :
    (kernelCoordinate b hb x₀ x).range.Normal :=
  WreathNormalBaseCoordinates.coordinate_range_normal
    (ActualBlockWreathEmbedding.embedding b hb x₀) (Kernel (A := G) (X := X))
    (kernel_le_wreath_top_kernel b hb x₀)
    (ActualBlockWreathEmbedding.fullComponent b hb x₀) x

/-- In particular every successive normal coordinate kernel has a
proved subnormal image in the actual primitive component. -/
theorem normal_kernel_coordinate_isSubnormal
    (N : Subgroup (Kernel (A := G) (X := X))) (hN : N.Normal) (x : X) :
    (N.map (kernelCoordinate b hb x₀ x)).IsSubnormal :=
  SubnormalCoordinateClassBound.map_normal_isSubnormal_of_range
    (kernelCoordinate b hb x₀ x) (kernelCoordinate_range_normal b hb x₀ x).isSubnormal N hN

/-- Only subnormal component budgets are consumed by the actual
ordinary coordinate-kernel filtration. -/
theorem kernel_genRank_le_subnormal_budget (c : ℕ)
    (hc : ∀ L : Subgroup (originalBlockComponent b hb x₀),
      L.IsSubnormal → MarkedC4.genRank L ≤ c) :
    MarkedC4.genRank (Kernel (A := G) (X := X)) ≤ Nat.card X * c := by
  letI : Fintype X := Fintype.ofFinite X
  have h := SubnormalCoordinateOrdinaryGenerators.genRank_le_finite_subnormal_coordinate_bounds
    (fun _ : X => originalBlockComponent b hb x₀) (fun _ => c)
    (Kernel (A := G) (X := X)) (kernelCoordinate b hb x₀)
    (fun x => (kernelCoordinate_range_normal b hb x₀ x).isSubnormal)
    (fun _ => hc) (kernelCoordinates_injective b hb x₀)
  simpa only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul,
    ←Nat.card_eq_fintype_card] using h

/-- A genuinely proved strict subnormal budget would suffice for the
ordinary half-degree step, even with a full S3 top. -/
theorem half_degree (c : ℕ)
    (hc : ∀ L : Subgroup (originalBlockComponent b hb x₀),
      L.IsSubnormal → MarkedC4.genRank L ≤ c)
    (hmargin : 2*c+2 ≤ Nat.card (originalBlockFibre b x₀))
    (ht : 2 ≤ Nat.card X) (hbelow : SmallerActionBound (Nat.card Ω)) :
    2 * MarkedC4.genRank G ≤ Nat.card Ω := by
  let r := Nat.card (originalBlockFibre b x₀)
  let t := Nat.card X
  have hproduct : r*t = Nat.card Ω := by
    have h := Nat.card_congr (ActualBlockWreathEmbedding.productEquiv b hb x₀)
    simpa only [Nat.card_prod] using h
  have ht' : 2 ≤ t := ht
  have hmargin' : 2*c+2 ≤ r := hmargin
  have hr : 2 ≤ r := by omega
  have htlt : Nat.card X < Nat.card Ω := by
    change t < Nat.card Ω
    nlinarith
  have hQ := rounded_rank_of_smaller (Nat.card Ω) hbelow
    (Top (A := G) (X := X)) X htlt
  have hK := kernel_genRank_le_subnormal_budget b hb x₀ c hc
  have hquot : MarkedC4.genRank (G ⧸ Kernel (A := G) (X := X)) =
      MarkedC4.genRank (Top (A := G) (X := X)) :=
    CoprimeNilpotentProductGenerators.genRank_mulEquiv
      (QuotientGroup.quotientKerEquivRange (topMap (A := G) (X := X)))
  have hG := MarkedC4.genRank_le_of_normal (Kernel (A := G) (X := X))
  rw [hquot] at hG
  have hcost : t*(2*c+2) ≤ t*r := Nat.mul_le_mul_left t hmargin'
  change MarkedC4.genRank (Kernel (A := G) (X := X)) ≤ t*c at hK
  change 2 * MarkedC4.genRank (Top (A := G) (X := X)) ≤ t+1 at hQ
  nlinarith

theorem exists_half_degree_generators (c : ℕ)
    (hc : ∀ L : Subgroup (originalBlockComponent b hb x₀),
      L.IsSubnormal → MarkedC4.genRank L ≤ c)
    (hmargin : 2*c+2 ≤ Nat.card (originalBlockFibre b x₀))
    (ht : 2 ≤ Nat.card X) (hbelow : SmallerActionBound (Nat.card Ω)) :
    ∃ S : Finset G, Subgroup.closure (S : Set G) = ⊤ ∧ 2 * S.card ≤ Nat.card Ω := by
  obtain ⟨S,hS,hgen⟩ := MarkedC4.genRank_spec (G := G)
  exact ⟨S,hgen,by rw [hS]; exact half_degree b hb x₀ c hc hmargin ht hbelow⟩

/-- Literal primitive-component installer. Its local strict budget
remains an explicit obligation; none of the small binary values is assumed. -/
theorem subgroup_half_degree_generators (n : ℕ) (J : Subgroup (Equiv.Perm (Fin n)))
    [MulAction.IsPretransitive J (Fin n)] (ω₀ : Fin n)
    (D : OriginalMinimalBlock (A := J) ω₀) (c : ℕ)
    (hc : ∀ L : Subgroup D.Component, L.IsSubnormal → MarkedC4.genRank L ≤ c)
    (hmargin : 2*c+2 ≤ Nat.card D.Fibre)
    (hbelow : ∀ (k : ℕ), k < n → ∀ L : Subgroup (Equiv.Perm (Fin k)),
      (k = 3 → L ≠ ⊤) →
        ∃ S : Finset L, Subgroup.closure (S : Set L) = ⊤ ∧ 2 * S.card ≤ k) :
    ∃ S : Finset J, Subgroup.closure (S : Set J) = ⊤ ∧ 2 * S.card ≤ n := by
  have hbase : SmallerActionBound (Nat.card (Fin n)) := by
    simpa only [Nat.card_fin] using smallerActionBound_of_subgroup_generators n hbelow
  have h := exists_half_degree_generators D.map D.map_equivariant D.base c
    hc hmargin D.degrees_ge_two.2 hbase
  simpa only [Nat.card_fin] using h

end SymmetricSubgroupAsymptotics.BlockSubnormalOrdinaryGeneratorInduction
