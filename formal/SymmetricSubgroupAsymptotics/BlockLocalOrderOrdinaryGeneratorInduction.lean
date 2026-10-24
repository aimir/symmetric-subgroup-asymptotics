import SymmetricSubgroupAsymptotics.ActualBlockWreathEmbedding
import SymmetricSubgroupAsymptotics.WreathNormalBaseCoordinates
import SymmetricSubgroupAsymptotics.FiniteCoordinateOrdinaryGenerators
import SymmetricSubgroupAsymptotics.FiniteGroupBinaryOrderGenerators
import SymmetricSubgroupAsymptotics.PermutationOrdinarySmallerActions
import SymmetricSubgroupAsymptotics.OriginalMinimalBlock
import Mathlib.Tactic.Linarith

/-! A strict order budget for the actual local component pays for any
smaller top action, including full S3. Coordinates of the actual kernel
come from its faithful original wreath embedding; independent base
factors or an affine splitting are not assumed. -/
set_option autoImplicit false
noncomputable section
open scoped Classical BigOperators
namespace SymmetricSubgroupAsymptotics.BlockLocalOrderOrdinaryGeneratorInduction
open OriginalBlockClassBound PermutationOrdinarySmallerActions

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

/-- Each coordinate is a homomorphism on the literal original kernel. -/
def kernelCoordinate (x : X) : Kernel (A := G) (X := X) →*
    originalBlockComponent b hb x₀ :=
  WreathNormalBaseCoordinates.coordinate (ActualBlockWreathEmbedding.embedding b hb x₀)
    (Kernel (A := G) (X := X)) (kernel_le_wreath_top_kernel b hb x₀) x

theorem kernelCoordinates_injective :
    Function.Injective (fun g : Kernel (A := G) (X := X) => fun x =>
      kernelCoordinate b hb x₀ x g) := by
  intro g h he
  apply Subtype.ext
  apply ActualBlockWreathEmbedding.embedding_injective b hb x₀
  apply PermutationalWreathProduct.ext
  · funext x
    exact congrFun he x
  · have hg : (ActualBlockWreathEmbedding.embedding b hb x₀ g.val).right = 1 :=
      kernel_le_wreath_top_kernel b hb x₀ g.property
    have hh : (ActualBlockWreathEmbedding.embedding b hb x₀ h.val).right = 1 :=
      kernel_le_wreath_top_kernel b hb x₀ h.property
    exact hg.trans hh.symm

/-- All actual coordinate subgroups inherit the same component order
budget. Ordinary rank is used throughout the coordinate filtration. -/
theorem kernel_genRank_le_of_component_order (c : ℕ)
    (hcard : Nat.card (originalBlockComponent b hb x₀) ≤ 2^c) :
    MarkedC4.genRank (Kernel (A := G) (X := X)) ≤ Nat.card X * c := by
  letI : Fintype X := Fintype.ofFinite X
  have hc : ∀ x : X, ∀ L : Subgroup (originalBlockComponent b hb x₀),
      MarkedC4.genRank L ≤ c := by
    intro _ L
    exact FiniteGroupBinaryOrderGenerators.genRank_le_of_card_le_two_pow L c
      (L.card_le_card_group.trans hcard)
  have h := FiniteCoordinateOrdinaryGenerators.genRank_le_finite_coordinate_sum
    (fun _ : X => originalBlockComponent b hb x₀) (fun _ => c) hc
    (Kernel (A := G) (X := X)) (kernelCoordinate b hb x₀)
    (kernelCoordinates_injective b hb x₀)
  simpa only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul,
    ←Nat.card_eq_fintype_card] using h

/-- A two-position margin in the actual fibre pays the rounded top
bound, without excluding a full three-point top image. -/
theorem half_degree (c : ℕ)
    (hcard : Nat.card (originalBlockComponent b hb x₀) ≤ 2^c)
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
  have hK := kernel_genRank_le_of_component_order b hb x₀ c hcard
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
    (hcard : Nat.card (originalBlockComponent b hb x₀) ≤ 2^c)
    (hmargin : 2*c+2 ≤ Nat.card (originalBlockFibre b x₀))
    (ht : 2 ≤ Nat.card X) (hbelow : SmallerActionBound (Nat.card Ω)) :
    ∃ S : Finset G, Subgroup.closure (S : Set G) = ⊤ ∧ 2 * S.card ≤ Nat.card Ω := by
  obtain ⟨S,hS,hgen⟩ := MarkedC4.genRank_spec (G := G)
  exact ⟨S,hgen,by rw [hS]; exact half_degree b hb x₀ c hcard hmargin ht hbelow⟩

/-- The literal original minimal block and its actual component remain
visible; the order and margin are local hypotheses only. -/
theorem subgroup_half_degree_generators (n : ℕ) (J : Subgroup (Equiv.Perm (Fin n)))
    [MulAction.IsPretransitive J (Fin n)] (ω₀ : Fin n)
    (D : OriginalMinimalBlock (A := J) ω₀) (c : ℕ)
    (hcard : Nat.card D.Component ≤ 2^c) (hmargin : 2*c+2 ≤ Nat.card D.Fibre)
    (hbelow : ∀ (k : ℕ), k < n → ∀ L : Subgroup (Equiv.Perm (Fin k)),
      (k = 3 → L ≠ ⊤) →
        ∃ S : Finset L, Subgroup.closure (S : Set L) = ⊤ ∧ 2 * S.card ≤ k) :
    ∃ S : Finset J, Subgroup.closure (S : Set J) = ⊤ ∧ 2 * S.card ≤ n := by
  have hbase : SmallerActionBound (Nat.card (Fin n)) := by
    simpa only [Nat.card_fin] using smallerActionBound_of_subgroup_generators n hbelow
  have h := exists_half_degree_generators D.map D.map_equivariant D.base c
    hcard hmargin D.degrees_ge_two.2 hbase
  simpa only [Nat.card_fin] using h

end SymmetricSubgroupAsymptotics.BlockLocalOrderOrdinaryGeneratorInduction
