import SymmetricSubgroupAsymptotics.C1CharacterWitness

/-! # Reversible inverse-complement incidences
The equivalence retains the literal ambient subgroup, oriented character and
order-three witness. In particular the inverse never chooses a kernel orbit.
-/
set_option autoImplicit false
noncomputable section
open scoped BigOperators Classical Pointwise
namespace SymmetricSubgroupAsymptotics
variable {G : Type*} [Group G]

abbrev TernaryWitness (χ : PrimeCharacters 3 G) :=
  {x : G // orderOf x = 3 ∧ χ (Additive.ofMul x) = 1}

abbrev TernaryIncidence (G : Type*) [Group G] :=
  Σ K : Subgroup G, Σ χ : PrimeCharacters 3 K, TernaryWitness χ

def ternaryIncidenceChart (d : TernaryIncidence G) : TernaryComplementChart G :=
  ternaryWitnessChart d.1 d.2.1 d.2.2.1 d.2.2.2.1 d.2.2.2.2

def ternaryChartIncidence (C : TernaryComplementChart G) : TernaryIncidence G :=
  ⟨C.source,C.character,⟨C.sourceGenerator,
    (Subgroup.orderOf_mk C.generator _).trans C.generator_order,C.character_generator⟩⟩

@[ext] theorem TernaryComplementChart.ext {C D : TernaryComplementChart G}
    (hk : C.kernel = D.kernel) (hx : C.generator = D.generator) : C = D := by
  cases C
  cases D
  cases hk
  cases hx
  rfl

theorem ternaryIncidenceChart_injective :
    Function.Injective (ternaryIncidenceChart (G := G)) := by
  rintro ⟨K,χ,x⟩ ⟨L,ψ,y⟩ h
  have hs := congrArg TernaryComplementChart.source h
  change (ternaryWitnessChart K χ x.1 x.2.1 x.2.2).source =
    (ternaryWitnessChart L ψ y.1 y.2.1 y.2.2).source at hs
  rw [ternaryWitnessChart_source,ternaryWitnessChart_source] at hs
  subst L
  have hx : x.1 = y.1 := Subtype.ext (congrArg TernaryComplementChart.generator h)
  have hk : (ternaryCharacterHom χ).ker = (ternaryCharacterHom ψ).ker :=
    Subgroup.map_injective K.subtype_injective
      (congrArg TernaryComplementChart.kernel h)
  have hχ := ternaryCharacter_ext_kernel_witness χ ψ hk x.1 x.2.2 (hx ▸ y.2.2)
  subst ψ
  have hxy : x = y := Subtype.ext hx
  cases hxy
  rfl

theorem ternaryIncidenceChart_chartIncidence (C : TernaryComplementChart G) :
    ternaryIncidenceChart (ternaryChartIncidence C) = C := by
  apply TernaryComplementChart.ext
  · change (ternaryCharacterHom C.character).ker.map C.source.subtype = C.kernel
    change C.characterHom.ker.map C.source.subtype = C.kernel
    rw [C.character_kernel,Subgroup.map_subgroupOf_eq_of_le
      (show C.kernel ≤ C.source from le_sup_left)]
  · rfl

theorem ternaryChartIncidence_incidenceChart (d : TernaryIncidence G) :
    ternaryChartIncidence (ternaryIncidenceChart d) = d :=
  ternaryIncidenceChart_injective
    (ternaryIncidenceChart_chartIncidence (ternaryIncidenceChart d))

/-- The exact literal (K, χ, x) ↔ (N, x) chart, with its original orientation. -/
def ternaryInverseComplementEquiv : TernaryIncidence G ≃ TernaryComplementChart G where
  toFun := ternaryIncidenceChart
  invFun := ternaryChartIncidence
  left_inv := ternaryChartIncidence_incidenceChart
  right_inv := ternaryIncidenceChart_chartIncidence

/-- An arbitrary survival condition on the complete original character pair
is transported through the exact reversible chart. -/
def ternaryInverseComplementSurvivalEquiv
    (S : (Σ K : Subgroup G, PrimeCharacters 3 K) → Prop) :
    {d : TernaryIncidence G // S ⟨d.1,d.2.1⟩} ≃
      {C : TernaryComplementChart G // S ⟨C.source,C.character⟩} :=
  (ternaryInverseComplementEquiv (G := G)).subtypeEquiv (fun d => by
    have h := congrArg (fun d : TernaryIncidence G => S ⟨d.1,d.2.1⟩)
      ((ternaryInverseComplementEquiv (G := G)).left_inv d)
    exact h.symm.to_iff)

end SymmetricSubgroupAsymptotics
