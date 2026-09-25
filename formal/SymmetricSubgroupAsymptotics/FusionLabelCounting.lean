import SymmetricSubgroupAsymptotics.OrbitProfileAssembly
import SymmetricSubgroupAsymptotics.FusionGoursat

/-!
# Original labelled orbit-pointing weights

The denominator comes from distinct original coordinate changes in each
literal physical subgroup fibre. Only stability of the local family under
those coordinate changes is needed; individual lifts need not be fixed.
-/

set_option autoImplicit false
noncomputable section
open scoped BigOperators

namespace SymmetricSubgroupAsymptotics

variable {X : Type*}

def FusionLabelledFamily (P : Subgroup (Equiv.Perm X) → Prop) :=
  Set.range (fun p : Equiv.Perm X × {K // P K} => relabelSubgroup p.1 p.2.1)

/-- An arbitrary supplied subgroup of original coordinate changes acts
on both the labels and the whole original local subgroup. -/
def FusionLabelNatural (S : Subgroup (Equiv.Perm X))
    (P : Subgroup (Equiv.Perm X) → Prop) : Prop :=
  ∀ s ∈ S, ∀ K, P K → P (relabelSubgroup s K)

theorem fusionLabelledFamily_mul_le [Finite X]
    (S : Subgroup (Equiv.Perm X)) (P : Subgroup (Equiv.Perm X) → Prop)
    (hP : FusionLabelNatural S P) :
    Nat.card (FusionLabelledFamily P) * Nat.card S ≤
      Nat.card (Equiv.Perm X) * Nat.card {K // P K} := by
  classical
  letI : Fintype (FusionLabelledFamily P) := Fintype.ofFinite _
  let f : Equiv.Perm X × {K // P K} → FusionLabelledFamily P :=
    fun p => ⟨relabelSubgroup p.1 p.2.1,⟨p,rfl⟩⟩
  have hlow (H : FusionLabelledFamily P) : Nat.card S ≤ Nat.card {p // f p=H} := by
    obtain ⟨p,hp⟩ := H.2
    let inject : S → {q // f q=H} := fun s =>
      ⟨(p.1*(s:Equiv.Perm X),
        ⟨relabelSubgroup (s:Equiv.Perm X)⁻¹ p.2.1,
          hP _ (S.inv_mem s.2) _ p.2.2⟩),by
        apply Subtype.ext
        change relabelSubgroup (p.1*(s:Equiv.Perm X))
          (relabelSubgroup (s:Equiv.Perm X)⁻¹ p.2.1)=H.1
        rw [relabelSubgroup_mul]
        simpa using hp⟩
    apply Nat.card_le_card_of_injective inject
    intro s t he
    apply Subtype.ext
    have hh := congrArg (fun q : {q // f q=H} => q.1.1) he
    exact mul_left_cancel hh
  have he := (Nat.card_congr (Equiv.sigmaFiberEquiv f)).symm
  rw [Nat.card_sigma,Nat.card_prod] at he
  calc
    _ = ∑ H : FusionLabelledFamily P, Nat.card S := by
      simp [Nat.card_eq_fintype_card]
    _ ≤ ∑ H : FusionLabelledFamily P, Nat.card {p // f p=H} :=
      Finset.sum_le_sum (fun H _ => hlow H)
    _ = _ := he.symm

/-- Full original label changes on one marked block and its entire
complement. The complementary action need not be transitive. -/
def fusionPointingSymmetryMap {Ω Z : Type*} (U : Subgroup (Equiv.Perm Ω)) :
    Subgroup.normalizer (U : Set (Equiv.Perm Ω)) × Equiv.Perm Z →*
      Equiv.Perm (Ω ⊕ Z) :=
  (Equiv.Perm.sumCongrHom Ω Z).comp
    ((Subgroup.normalizer (U : Set (Equiv.Perm Ω))).subtype.prodMap (MonoidHom.id _))

theorem fusionPointingSymmetryMap_injective {Ω Z : Type*}
    (U : Subgroup (Equiv.Perm Ω)) :
    Function.Injective (fusionPointingSymmetryMap (Z := Z) U) := by
  intro x y he
  have h := Equiv.Perm.sumCongrHom_injective he
  change ((x.1 : Equiv.Perm Ω),x.2)=((y.1 : Equiv.Perm Ω),y.2) at h
  apply Prod.ext
  · exact Subtype.ext (congrArg Prod.fst h)
  · exact congrArg (fun z : Equiv.Perm Ω × Equiv.Perm Z => z.2) h

def fusionPointingSymmetries {Ω Z : Type*} (U : Subgroup (Equiv.Perm Ω)) :
    Subgroup (Equiv.Perm (Ω ⊕ Z)) :=
  (fusionPointingSymmetryMap (Z := Z) U).range

/-- The proved divisor uses the original action normalizer and every
permutation of the complete complement. -/
theorem fusionPointingSymmetries_card {Ω Z : Type*} [Finite Ω] [Fintype Z]
    (U : Subgroup (Equiv.Perm Ω)) :
    Nat.card (fusionPointingSymmetries (Z := Z) U) =
      Nat.card (Subgroup.normalizer (U : Set (Equiv.Perm Ω))) * (Fintype.card Z).factorial := by
  classical
  change Nat.card (Set.range (fusionPointingSymmetryMap (Z := Z) U)) = _
  rw [← Nat.card_congr (Equiv.ofInjective (fusionPointingSymmetryMap (Z := Z) U)
    (fusionPointingSymmetryMap_injective U))]
  simp [Nat.card_prod,Nat.card_eq_fintype_card,Fintype.card_perm]

/-- Physical original-weight pointing bound. A fixed axis is not silently
declared stable under the full normalizer: the actual accepted local family
must have the displayed coordinate-change stability. -/
theorem fusion_original_pointing_bound {Ω Z : Type*} [Fintype Ω] [Fintype Z]
    (U : Subgroup (Equiv.Perm Ω))
    (P : Subgroup (Equiv.Perm (Ω ⊕ Z)) → Prop)
    (hP : FusionLabelNatural (fusionPointingSymmetries U) P) :
    (Nat.card (FusionLabelledFamily P) : ℝ) ≤
      ((Fintype.card Ω+Fintype.card Z).factorial : ℝ) /
        ((Fintype.card Z).factorial *
          (Nat.card (Subgroup.normalizer (U : Set (Equiv.Perm Ω))) : ℝ)) *
            Nat.card {K // P K} := by
  classical
  have h := fusionLabelledFamily_mul_le (fusionPointingSymmetries U) P hP
  rw [fusionPointingSymmetries_card] at h
  have hn : Nat.card (Equiv.Perm (Ω ⊕ Z)) =
      (Fintype.card Ω+Fintype.card Z).factorial := by
    simp [Nat.card_eq_fintype_card,Fintype.card_perm]
  rw [hn] at h
  have hd : (0 : ℝ) < (Fintype.card Z).factorial *
      (Nat.card (Subgroup.normalizer (U : Set (Equiv.Perm Ω))) : ℝ) := by
    exact mul_pos (by exact_mod_cast Nat.factorial_pos _) (by exact_mod_cast Nat.card_pos)
  rw [div_mul_eq_mul_div]
  apply (le_div_iff₀ hd).mpr
  have hr : (Nat.card (FusionLabelledFamily P) : ℝ) *
      ((Nat.card (Subgroup.normalizer (U : Set (Equiv.Perm Ω))) : ℝ) *
        (Fintype.card Z).factorial) ≤
      ((Fintype.card Ω+Fintype.card Z).factorial : ℝ) * Nat.card {K // P K} := by
    exact_mod_cast h
  convert hr using 1
  ring

end SymmetricSubgroupAsymptotics
