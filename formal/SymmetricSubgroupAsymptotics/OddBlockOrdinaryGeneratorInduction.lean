import SymmetricSubgroupAsymptotics.FiniteCoordinateOrdinaryGenerators
import SymmetricSubgroupAsymptotics.BlockKernelClassBound
import SymmetricSubgroupAsymptotics.TransitiveBlockQuotient
import SymmetricSubgroupAsymptotics.PermutationOrdinarySmallerActions
import Mathlib.Algebra.Ring.Parity
import Mathlib.Tactic.Linarith

/-! An ordinary-generator induction step for actual equivariant block
maps with odd fibre size at least five and nonexceptional top degree.
The kernel is kept as its actual correlated family of fibre actions.
The result uses the sharp theorem only at strictly smaller degrees.
Even fibres, three-point fibres and a full S3 top are not resolved here. -/
set_option autoImplicit false
noncomputable section
open scoped BigOperators Classical
namespace SymmetricSubgroupAsymptotics.OddBlockOrdinaryGeneratorInduction
open OriginalBlockClassBound PermutationOrdinarySmallerActions

variable {G Ω X : Type} [Group G] [Finite G] [Finite Ω] [Finite X]
    [MulAction G Ω] [MulAction G X] [FaithfulSMul G Ω]

private def fibreTransport (b : Ω→X) (hb : ∀(g : G) (ω : Ω),b (g•ω)=g•b ω)
    (g : G) (x : X) : originalBlockFibre b x ≃ originalBlockFibre b (g•x) where
  toFun ω := ⟨g•ω.val,by rw [hb,ω.property]⟩
  invFun ω := ⟨g⁻¹•ω.val,by rw [hb,ω.property,inv_smul_smul]⟩
  left_inv ω := Subtype.ext (inv_smul_smul g ω.val)
  right_inv ω := Subtype.ext (smul_inv_smul g ω.val)

omit [Finite G] [Finite Ω] [Finite X] [FaithfulSMul G Ω] in
private theorem fibre_card_eq [MulAction.IsPretransitive G X]
    (b : Ω→X) (hb : ∀(g : G) (ω : Ω),b (g•ω)=g•b ω) (x₀ x : X) :
    Nat.card (originalBlockFibre b x)=Nat.card (originalBlockFibre b x₀) := by
  obtain ⟨g,rfl⟩ := MulAction.exists_smul_eq G x₀ x
  exact (Nat.card_congr (fibreTransport b hb g x₀)).symm

private theorem degree_product [MulAction.IsPretransitive G X]
    (b : Ω→X) (hb : ∀(g : G) (ω : Ω),b (g•ω)=g•b ω) (x₀ : X) :
    Nat.card X*Nat.card (originalBlockFibre b x₀)=Nat.card Ω := by
  letI : Fintype X := Fintype.ofFinite X
  have he := Nat.card_congr (Equiv.sigmaFiberEquiv b)
  rw [Nat.card_sigma] at he
  simpa only [fibre_card_eq b hb x₀,Finset.sum_const,Finset.card_univ,
    nsmul_eq_mul,←Nat.card_eq_fintype_card] using he

/-- The actual block kernel has the sum of ordinary subgroup budgets
of its literal fibres. No independent product or normal rank is used. -/
theorem kernel_genRank_le (b : Ω→X) (hb : ∀(g : G) (ω : Ω),b (g•ω)=g•b ω) (c : ℕ)
    (hc : ∀x (L : Subgroup (Equiv.Perm (originalBlockFibre b x))),
      MarkedC4.genRank L ≤ c) :
    MarkedC4.genRank (Kernel (A:=G) (X:=X)) ≤ Nat.card X*c := by
  letI : Fintype X := Fintype.ofFinite X
  have hh := FiniteCoordinateOrdinaryGenerators.genRank_le_finite_coordinate_sum
    (fun x=>Equiv.Perm (originalBlockFibre b x)) (fun _=>c) hc
    (Kernel (A:=G) (X:=X)) (coordinate b hb) (coordinates_injective b hb)
  simpa only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul,
    ←Nat.card_eq_fintype_card] using hh

/-- Odd fibre rounding pays for the top action. The full degree-three
top is explicitly excluded; no degree-n induction premise is present. -/
theorem half_degree_of_odd_fibres [MulAction.IsPretransitive G X]
    (b : Ω→X) (hb : ∀(g : G) (ω : Ω),b (g•ω)=g•b ω) (x₀ : X)
    (hodd : Odd (Nat.card (originalBlockFibre b x₀)))
    (hr : 5 ≤ Nat.card (originalBlockFibre b x₀)) (ht : 2 ≤ Nat.card X)
    (hthree : Nat.card X≠3) (hbelow : SmallerActionBound (Nat.card Ω)) :
    2*MarkedC4.genRank G ≤ Nat.card Ω := by
  let r := Nat.card (originalBlockFibre b x₀)
  let t := Nat.card X
  have hproduct : t*r=Nat.card Ω := degree_product b hb x₀
  have hrlt : r < Nat.card Ω := by dsimp only [r,t] at *; nlinarith
  have htlt : t < Nat.card Ω := by dsimp only [r,t] at *; nlinarith
  have hlocal : ∀x (L : Subgroup (Equiv.Perm (originalBlockFibre b x))),
      MarkedC4.genRank L ≤ r/2 := by
    intro x L
    have hx := fibre_card_eq b hb x₀ x
    have hbound := hbelow L (originalBlockFibre b x)
      (by rw [hx]; exact hrlt) (by rw [hx]; omega)
    dsimp only [r]
    omega
  have hK := kernel_genRank_le b hb (r/2) hlocal
  let π : G→*Top (A:=G) (X:=X) := (topMap (A:=G) (X:=X)).rangeRestrict
  have hπ : Function.Surjective π :=
    (topMap (A:=G) (X:=X)).rangeRestrict_surjective
  letI : Finite (Top (A:=G) (X:=X)) := Finite.of_surjective π hπ
  have hQ := hbelow (Top (A:=G) (X:=X)) X htlt hthree
  have hquot : MarkedC4.genRank (G⧸Kernel (A:=G) (X:=X))=
      MarkedC4.genRank (Top (A:=G) (X:=X)) :=
    CoprimeNilpotentProductGenerators.genRank_mulEquiv
      (QuotientGroup.quotientKerEquivRange (topMap (A:=G) (X:=X)))
  have hG := MarkedC4.genRank_le_of_normal (Kernel (A:=G) (X:=X))
  rw [hquot] at hG
  have hround : 2*(r/2)+1=r := Nat.two_mul_div_two_add_one_of_odd hodd
  change MarkedC4.genRank (Kernel (A:=G) (X:=X)) ≤ t*(r/2) at hK
  change 2*MarkedC4.genRank (Top (A:=G) (X:=X)) ≤ t at hQ
  nlinarith

theorem exists_half_degree_generators [MulAction.IsPretransitive G X]
    (b : Ω→X) (hb : ∀(g : G) (ω : Ω),b (g•ω)=g•b ω) (x₀ : X)
    (hodd : Odd (Nat.card (originalBlockFibre b x₀)))
    (hr : 5 ≤ Nat.card (originalBlockFibre b x₀)) (ht : 2 ≤ Nat.card X)
    (hthree : Nat.card X≠3) (hbelow : SmallerActionBound (Nat.card Ω)) :
    ∃S:Finset G,Subgroup.closure (S:Set G)=⊤ ∧ 2*S.card ≤ Nat.card Ω := by
  obtain ⟨S,hS,hgen⟩ := MarkedC4.genRank_spec (G:=G)
  exact ⟨S,hgen,by rw [hS]; exact half_degree_of_odd_fibres b hb x₀ hodd hr ht hthree hbelow⟩

/-- A literal transitive imprimitive subgroup with an actual proper
point-stabilizer overgroup. Its original degree n is retained. -/
theorem subgroup_half_degree_generators (n : ℕ) (J : Subgroup (Equiv.Perm (Fin n)))
    (htrans : MulAction.IsPretransitive J (Fin n)) (ω₀ : Fin n) (H : Subgroup J)
    (hH : MulAction.stabilizer J ω₀ < H) (hHt : H < ⊤)
    (hodd : Odd ((MulAction.stabilizer J ω₀).relIndex H))
    (hr : 5 ≤ (MulAction.stabilizer J ω₀).relIndex H) (hthree : H.index≠3)
    (hbelow : ∀(k : ℕ),k<n→∀L:Subgroup (Equiv.Perm (Fin k)),
      (k=3→L≠⊤)→∃S:Finset L,Subgroup.closure (S:Set L)=⊤ ∧ 2*S.card ≤ k) :
    ∃S:Finset J,Subgroup.closure (S:Set J)=⊤ ∧ 2*S.card ≤ n := by
  letI : MulAction.IsPretransitive J (Fin n) := htrans
  let b := originalTransitiveBlockMap ω₀ H
  have hb := originalTransitiveBlockMap_equivariant ω₀ H hH.le
  have hcard : Nat.card (originalBlockFibre b ((1:J):J⧸H)) =
      (MulAction.stabilizer J ω₀).relIndex H :=
    originalTransitiveBlockFibre_card ω₀ H hH.le
  have htwo := originalTransitiveBlock_factors_ge_two ω₀ H hH hHt
  have hbase : SmallerActionBound (Nat.card (Fin n)) := by
    simpa only [Nat.card_fin] using smallerActionBound_of_subgroup_generators n hbelow
  have hh := exists_half_degree_generators b hb ((1:J):J⧸H)
    (by rw [hcard]; exact hodd) (by rw [hcard]; exact hr)
    htwo.2 hthree hbase
  simpa only [Nat.card_fin] using hh

end SymmetricSubgroupAsymptotics.OddBlockOrdinaryGeneratorInduction
