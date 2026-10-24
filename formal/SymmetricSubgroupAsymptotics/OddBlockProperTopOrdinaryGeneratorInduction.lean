import SymmetricSubgroupAsymptotics.OddBlockOrdinaryGeneratorInduction
import SymmetricSubgroupAsymptotics.PermutationOrdinarySmallerImage
import SymmetricSubgroupAsymptotics.OriginalMinimalBlock

/-! Odd fibres of size at least five need only exclude the actual
full three-point top image, rather than excluding every three-point
top. The original correlated kernel and original point degree are kept;
the induction premise is exclusively at strictly smaller degrees. -/
set_option autoImplicit false
noncomputable section
open scoped Classical BigOperators
namespace SymmetricSubgroupAsymptotics.OddBlockProperTopOrdinaryGeneratorInduction
open OriginalBlockClassBound PermutationOrdinarySmallerActions

variable {G Ω X : Type} [Group G] [Finite G] [Finite Ω] [Finite X]
    [MulAction G Ω] [MulAction G X] [FaithfulSMul G Ω]

private def fibreTransport
    (b : Ω → X) (hb : ∀ (g : G) (ω : Ω), b (g • ω) = g • b ω)
    (g : G) (x : X) : originalBlockFibre b x ≃ originalBlockFibre b (g • x) where
  toFun ω := ⟨g • ω.val,by rw [hb,ω.property]⟩
  invFun ω := ⟨g⁻¹ • ω.val,by rw [hb,ω.property,inv_smul_smul]⟩
  left_inv ω := Subtype.ext (inv_smul_smul g ω.val)
  right_inv ω := Subtype.ext (smul_inv_smul g ω.val)

omit [Finite G] [Finite Ω] [Finite X] [FaithfulSMul G Ω] in
private theorem fibre_card_eq [MulAction.IsPretransitive G X]
    (b : Ω → X) (hb : ∀ (g : G) (ω : Ω), b (g • ω) = g • b ω) (x₀ x : X) :
    Nat.card (originalBlockFibre b x) = Nat.card (originalBlockFibre b x₀) := by
  obtain ⟨g,rfl⟩ := MulAction.exists_smul_eq G x₀ x
  exact (Nat.card_congr (fibreTransport b hb g x₀)).symm

private theorem degree_product [MulAction.IsPretransitive G X]
    (b : Ω → X) (hb : ∀ (g : G) (ω : Ω), b (g • ω) = g • b ω) (x₀ : X) :
    Nat.card X * Nat.card (originalBlockFibre b x₀) = Nat.card Ω := by
  letI : Fintype X := Fintype.ofFinite X
  have he := Nat.card_congr (Equiv.sigmaFiberEquiv b)
  rw [Nat.card_sigma] at he
  simpa only [fibre_card_eq b hb x₀,Finset.sum_const,Finset.card_univ,
    nsmul_eq_mul,←Nat.card_eq_fintype_card] using he

/-- The actual top image may have degree three; only its equality to
the full symmetric group is excluded at that degree. -/
theorem half_degree [MulAction.IsPretransitive G X]
    (b : Ω → X) (hb : ∀ (g : G) (ω : Ω), b (g • ω) = g • b ω) (x₀ : X)
    (hodd : Odd (Nat.card (originalBlockFibre b x₀)))
    (hr : 5 ≤ Nat.card (originalBlockFibre b x₀)) (ht : 2 ≤ Nat.card X)
    (hproper : Nat.card X = 3 → Top (A := G) (X := X) ≠ ⊤)
    (hbelow : ∀ (k : ℕ), k < Nat.card Ω → ∀ L : Subgroup (Equiv.Perm (Fin k)),
      (k = 3 → L ≠ ⊤) →
        ∃ S : Finset L, Subgroup.closure (S : Set L) = ⊤ ∧ 2 * S.card ≤ k) :
    2 * MarkedC4.genRank G ≤ Nat.card Ω := by
  let r := Nat.card (originalBlockFibre b x₀)
  let t := Nat.card X
  have hproduct : t * r = Nat.card Ω := degree_product b hb x₀
  have hrlt : r < Nat.card Ω := by dsimp only [r,t] at *; nlinarith
  have htlt : t < Nat.card Ω := by dsimp only [r,t] at *; nlinarith
  have hsmall : SmallerActionBound (Nat.card Ω) :=
    smallerActionBound_of_subgroup_generators (Nat.card Ω) hbelow
  have hlocal : ∀ x (L : Subgroup (Equiv.Perm (originalBlockFibre b x))),
      MarkedC4.genRank L ≤ r / 2 := by
    intro x L
    have hx := fibre_card_eq b hb x₀ x
    have hbound := hsmall L (originalBlockFibre b x)
      (by rw [hx]; exact hrlt) (by rw [hx]; omega)
    dsimp only [r]
    omega
  have hK := OddBlockOrdinaryGeneratorInduction.kernel_genRank_le b hb (r / 2) hlocal
  have hQ := PermutationOrdinarySmallerImage.genRank_of_smaller_image
    (Nat.card Ω) hbelow (Top (A := G) (X := X)) htlt hproper
  have hquot : MarkedC4.genRank (G ⧸ Kernel (A := G) (X := X)) =
      MarkedC4.genRank (Top (A := G) (X := X)) :=
    CoprimeNilpotentProductGenerators.genRank_mulEquiv
      (QuotientGroup.quotientKerEquivRange (topMap (A := G) (X := X)))
  have hG := MarkedC4.genRank_le_of_normal (Kernel (A := G) (X := X))
  rw [hquot] at hG
  have hround : 2 * (r / 2) + 1 = r := Nat.two_mul_div_two_add_one_of_odd hodd
  change MarkedC4.genRank (Kernel (A := G) (X := X)) ≤ t * (r / 2) at hK
  change 2 * MarkedC4.genRank (Top (A := G) (X := X)) ≤ t at hQ
  nlinarith

theorem exists_half_degree_generators [MulAction.IsPretransitive G X]
    (b : Ω → X) (hb : ∀ (g : G) (ω : Ω), b (g • ω) = g • b ω) (x₀ : X)
    (hodd : Odd (Nat.card (originalBlockFibre b x₀)))
    (hr : 5 ≤ Nat.card (originalBlockFibre b x₀)) (ht : 2 ≤ Nat.card X)
    (hproper : Nat.card X = 3 → Top (A := G) (X := X) ≠ ⊤)
    (hbelow : ∀ (k : ℕ), k < Nat.card Ω → ∀ L : Subgroup (Equiv.Perm (Fin k)),
      (k = 3 → L ≠ ⊤) →
        ∃ S : Finset L, Subgroup.closure (S : Set L) = ⊤ ∧ 2 * S.card ≤ k) :
    ∃ S : Finset G, Subgroup.closure (S : Set G) = ⊤ ∧ 2 * S.card ≤ Nat.card Ω := by
  obtain ⟨S,hS,hgen⟩ := MarkedC4.genRank_spec (G := G)
  exact ⟨S,hgen,by rw [hS]; exact half_degree b hb x₀ hodd hr ht hproper hbelow⟩

/-- Literal original minimal-block installer. The guard names the
actual quotient permutation image, with no C3 chart or image census. -/
theorem subgroup_half_degree_generators (n : ℕ) (J : Subgroup (Equiv.Perm (Fin n)))
    [MulAction.IsPretransitive J (Fin n)] (ω₀ : Fin n)
    (D : OriginalMinimalBlock (A := J) ω₀)
    (hodd : Odd (Nat.card D.Fibre)) (hr : 5 ≤ Nat.card D.Fibre)
    (hproper : Nat.card D.Points = 3 → D.Top ≠ ⊤)
    (hbelow : ∀ (k : ℕ), k < n → ∀ L : Subgroup (Equiv.Perm (Fin k)),
      (k = 3 → L ≠ ⊤) →
        ∃ S : Finset L, Subgroup.closure (S : Set L) = ⊤ ∧ 2 * S.card ≤ k) :
    ∃ S : Finset J, Subgroup.closure (S : Set J) = ⊤ ∧ 2 * S.card ≤ n := by
  have hbase : ∀ (k : ℕ), k < Nat.card (Fin n) → ∀ L : Subgroup (Equiv.Perm (Fin k)),
      (k = 3 → L ≠ ⊤) →
        ∃ S : Finset L, Subgroup.closure (S : Set L) = ⊤ ∧ 2 * S.card ≤ k := by
    simpa only [Nat.card_fin] using hbelow
  have hh := exists_half_degree_generators D.map D.map_equivariant D.base
    hodd hr D.degrees_ge_two.2 hproper hbase
  simpa only [Nat.card_fin] using hh

end SymmetricSubgroupAsymptotics.OddBlockProperTopOrdinaryGeneratorInduction
