import SymmetricSubgroupAsymptotics.C1SplitCharacters
import SymmetricSubgroupAsymptotics.FusionGoursat

/-! # Exact c=1 surviving literal graphs
The external oriented ternary character and the complete original source
inject into actual subgroups of C3 × G. Every survival predicate is evaluated
on that full subgroup, before any upper bound on its character weight.
-/
set_option autoImplicit false
noncomputable section
open scoped BigOperators Classical
namespace SymmetricSubgroupAsymptotics
variable {G : Type*} [Group G]

abbrev TernaryGraphData (G : Type*) [Group G] :=
  Σ K : Subgroup G, PrimeCharacters 3 K

def ternaryActualGraph (d : TernaryGraphData G) : Subgroup (TernaryCyclic × G) :=
  fusionQuotientGraph (MonoidHom.id TernaryCyclic) d.1 (ternaryCharacterHom d.2)

theorem ternaryActualGraph_complement (d : TernaryGraphData G) :
    (ternaryActualGraph d).map (MonoidHom.snd TernaryCyclic G) = d.1 :=
  fusionQuotientGraph_complement _ Function.surjective_id _ _

theorem ternaryActualGraph_injective :
    Function.Injective (ternaryActualGraph (G := G)) := by
  rintro ⟨K,χ⟩ ⟨L,ψ⟩ h
  have hK := congrArg (fun H : Subgroup (TernaryCyclic×G) =>
    H.map (MonoidHom.snd TernaryCyclic G)) h
  dsimp only at hK
  rw [ternaryActualGraph_complement,ternaryActualGraph_complement] at hK
  change K = L at hK
  subst L
  have hχ : χ=ψ := by
    apply AddMonoidHom.toMultiplicativeRight.injective
    apply MonoidHom.ext
    intro k
    have hm : (ternaryCharacterHom χ k,(k:G)) ∈ ternaryActualGraph ⟨K,χ⟩ :=
      (fusionQuotientGraph_fibre _ _ _ _ k).mpr rfl
    rw [h] at hm
    exact (fusionQuotientGraph_fibre _ _ _ _ k).mp hm
  subst ψ
  rfl

theorem ternarySplit_character_surjective (χ : PrimeCharacters 3 G)
    (hχ : TernarySplit χ) : Function.Surjective (ternaryCharacterHom χ) := by
  obtain ⟨s,hs⟩ := hχ
  exact fun y => ⟨s y,DFunLike.congr_fun hs y⟩

theorem ternaryActualGraph_full (d : TernaryGraphData G) (hd : TernarySplit d.2) :
    (ternaryActualGraph d).map (MonoidHom.fst TernaryCyclic G) = ⊤ :=
  fusionQuotientGraph_full _ _ _ (ternarySplit_character_surjective d.2 hd)

def TernarySurvivingGraphs (P : Subgroup (TernaryCyclic × G) → Prop) :=
  Set.range (fun d : {d : TernaryGraphData G // TernarySplit d.2 ∧ P (ternaryActualGraph d)} =>
    ternaryActualGraph d.1)

theorem ternarySurvivingGraphs_parameter_card
    (P : Subgroup (TernaryCyclic × G) → Prop) :
    Nat.card (TernarySurvivingGraphs P) =
      Nat.card {d : TernaryGraphData G // TernarySplit d.2 ∧ P (ternaryActualGraph d)} := by
  exact (Nat.card_congr (Equiv.ofInjective
    (fun d : {d : TernaryGraphData G // TernarySplit d.2 ∧ P (ternaryActualGraph d)} =>
      ternaryActualGraph d.1)
    (fun _ _ h => Subtype.ext (ternaryActualGraph_injective h)))).symm

/-- The exact surviving character sum for the original complete graph family.
No unmarked residual count is substituted for the literal character weight. -/
theorem ternarySurvivingGraphs_card [Finite G]
    (P : Subgroup (TernaryCyclic × G) → Prop) :
    letI := Fintype.ofFinite (Subgroup G)
    Nat.card (TernarySurvivingGraphs P) =
      ∑ K : Subgroup G,
        ternarySurvivingWeight (fun χ : PrimeCharacters 3 K => P (ternaryActualGraph ⟨K,χ⟩)) := by
  letI := Fintype.ofFinite (Subgroup G)
  let e := Equiv.ofInjective
    (fun d : {d : TernaryGraphData G // TernarySplit d.2 ∧ P (ternaryActualGraph d)} =>
      ternaryActualGraph d.1)
    (fun _ _ h => Subtype.ext (ternaryActualGraph_injective h))
  let ee : {d : TernaryGraphData G // TernarySplit d.2 ∧ P (ternaryActualGraph d)} ≃
      (Σ K : Subgroup G, {χ : PrimeCharacters 3 K //
        TernarySplit χ ∧ P (ternaryActualGraph ⟨K,χ⟩)}) :=
    { toFun := fun d => ⟨d.1.1,⟨d.1.2,d.2⟩⟩
      invFun := fun d => ⟨⟨d.1,d.2.1⟩,d.2.2⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  change Nat.card (Set.range _) = _
  rw [← Nat.card_congr e,Nat.card_congr ee]
  letI (K : Subgroup G) := Fintype.ofFinite {χ : PrimeCharacters 3 K //
    TernarySplit χ ∧ P (ternaryActualGraph ⟨K,χ⟩)}
  simp only [Nat.card_eq_fintype_card,Fintype.card_sigma,ternarySurvivingWeight]

end SymmetricSubgroupAsymptotics
