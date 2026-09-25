import SymmetricSubgroupAsymptotics.C1InverseComplementCount
import SymmetricSubgroupAsymptotics.C1ActualGraphs

/-! # The literal inverse-complement denominator
The reciprocal denominator is the number of order-three elements in the
original coset N x, with no quotient by conjugacy or cancellation of witnesses.
-/
set_option autoImplicit false
noncomputable section
open scoped BigOperators Classical
namespace SymmetricSubgroupAsymptotics
variable {G : Type*} [Group G]
namespace TernaryComplementChart
variable (C : TernaryComplementChart G)

def coset : Set G := {y | ∃ n ∈ C.kernel, n * C.generator = y}

abbrev CosetWitness := {y : G // y ∈ C.coset ∧ orderOf y = 3}

theorem coset_mem_source {y : G} (hy : y ∈ C.coset) : y ∈ C.source := by
  obtain ⟨n,hn,rfl⟩ := hy
  exact C.source.mul_mem ((show C.kernel ≤ C.source from le_sup_left) hn)
    C.sourceGenerator.2

theorem coset_character {y : G} (hy : y ∈ C.coset) :
    C.character (Additive.ofMul (⟨y,C.coset_mem_source hy⟩ : C.source)) = 1 := by
  obtain ⟨n,hn,rfl⟩ := hy
  let n' : C.source := ⟨n,(show C.kernel ≤ C.source from le_sup_left) hn⟩
  have hn' : C.characterHom n' = 1 := by
    change n' ∈ C.characterHom.ker
    rw [C.character_kernel]
    exact hn
  have he : (⟨n*C.generator,C.coset_mem_source ⟨n,hn,rfl⟩⟩ : C.source) =
      n'*C.sourceGenerator := rfl
  change (C.characterHom ⟨n*C.generator,_⟩).toAdd = 1
  rw [he,C.characterHom.map_mul,hn',one_mul]
  exact C.character_generator

theorem character_mem_coset (y : C.source)
    (hy : C.character (Additive.ofMul y) = 1) : (y : G) ∈ C.coset := by
  have hx : C.characterHom C.sourceGenerator = ternaryGenerator :=
    congrArg Multiplicative.ofAdd C.character_generator
  have hy' : C.characterHom y = ternaryGenerator := congrArg Multiplicative.ofAdd hy
  have hn : y*C.sourceGenerator⁻¹ ∈ C.characterHom.ker := by
    change C.characterHom (y*C.sourceGenerator⁻¹) = 1
    rw [C.characterHom.map_mul,C.characterHom.map_inv,hy',hx,mul_inv_cancel]
  rw [C.character_kernel] at hn
  refine ⟨(y:G)*C.generator⁻¹,hn,?_⟩
  exact inv_mul_cancel_right _ _

def cosetWitnessEquiv : TernaryWitness C.character ≃ C.CosetWitness where
  toFun y := ⟨y.1,C.character_mem_coset y.1 y.2.2,
    (Subgroup.orderOf_mk y.1.1 y.1.2).symm.trans y.2.1⟩
  invFun y := ⟨⟨y.1,C.coset_mem_source y.2.1⟩,
    (Subgroup.orderOf_mk y.1 _).trans y.2.2,C.coset_character y.2.1⟩
  left_inv := by intro y; rfl
  right_inv := by intro y; rfl

theorem witnessCount_eq_cosetCount :
    ternaryWitnessCount C.character = Nat.card C.CosetWitness :=
  Nat.card_congr C.cosetWitnessEquiv

end TernaryComplementChart

/-- The manuscript's exact surviving inverse-complement formula over all
literal (N,x) charts. The original reciprocal is retained. -/
theorem ternaryInverseComplement_coset_reciprocal [Finite G]
    (S : (Σ K : Subgroup G, PrimeCharacters 3 K) → Prop) :
    letI := Fintype.ofFinite {C : TernaryComplementChart G // S ⟨C.source,C.character⟩}
    (Nat.card (TernarySurvivingPair S) : ℚ) =
      ∑ C : {C : TernaryComplementChart G // S ⟨C.source,C.character⟩},
        ((Nat.card C.1.CosetWitness : ℚ))⁻¹ := by
  rw [ternaryInverseComplement_reciprocal S]
  apply Finset.sum_congr rfl
  intro C _
  rw [C.1.witnessCount_eq_cosetCount]

/-- Required c=1 audit specialized to survival of the actual original graph.
The reciprocal still counts every literal coset witness on the same source. -/
theorem ternarySurvivingGraphs_coset_reciprocal [Finite G]
    (P : Subgroup (TernaryCyclic × G) → Prop) :
    letI := Fintype.ofFinite {C : TernaryComplementChart G //
      P (ternaryActualGraph ⟨C.source,C.character⟩)}
    (Nat.card (TernarySurvivingGraphs P) : ℚ) =
      ∑ C : {C : TernaryComplementChart G //
          P (ternaryActualGraph ⟨C.source,C.character⟩)},
        ((Nat.card C.1.CosetWitness : ℚ))⁻¹ := by
  rw [ternarySurvivingGraphs_parameter_card]
  exact ternaryInverseComplement_coset_reciprocal (fun d => P (ternaryActualGraph d))

end SymmetricSubgroupAsymptotics
