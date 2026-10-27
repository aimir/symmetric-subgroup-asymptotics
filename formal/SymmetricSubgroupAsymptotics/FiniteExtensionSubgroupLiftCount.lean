import Mathlib.Algebra.Group.Subgroup.Finite
import Mathlib.GroupTheory.QuotientGroup.Basic
import Mathlib.SetTheory.Cardinal.Finite

/-! ALL subgroup lifts in an arbitrary finite extension, at fixed image
and literal kernel intersection. No splitting or abelianness is assumed.
A kernel and image do not determine a subgroup; its actual generator lifts
are retained, and counted by differences in the original extension kernel. -/
set_option autoImplicit false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics.FiniteExtensionSubgroupLiftCount

variable {E Q : Type} [Group E] [Group Q]

abbrev LiftFamily (π : E →* Q) (K : Subgroup E) :=
  {L : Subgroup E // L.map π=⊤ ∧ L⊓π.ker=K}

private theorem exists_lift (π : E →* Q) (K : Subgroup E)
    {d : ℕ} (f : Fin d → Q) (L : LiftFamily π K) (i : Fin d) :
    ∃ g : L.val,π g=f i := by
  have hh : f i∈L.val.map π := by rw [L.property.1]; exact Subgroup.mem_top _
  obtain ⟨g,hg,he⟩ := hh
  exact ⟨⟨g,hg⟩,he⟩

private def selectedLift (π : E →* Q) (K : Subgroup E)
    {d : ℕ} (f : Fin d → Q) (L : LiftFamily π K) (i : Fin d) : E :=
  (Classical.choose (exists_lift π K f L i) : L.val)

private theorem selectedLift_mem (π : E →* Q) (K : Subgroup E)
    {d : ℕ} (f : Fin d → Q) (L : LiftFamily π K) (i : Fin d) :
    selectedLift π K f L i∈L.val :=
  (Classical.choose (exists_lift π K f L i)).property

private theorem selectedLift_map (π : E →* Q) (K : Subgroup E)
    {d : ℕ} (f : Fin d → Q) (L : LiftFamily π K) (i : Fin d) :
    π (selectedLift π K f L i)=f i :=
  Classical.choose_spec (exists_lift π K f L i)

/-- The WHOLE subgroup is recovered, including every nonsplit lift fibre. -/
theorem closure_kernel_union_lifts (π : E →* Q) (K : Subgroup E)
    {d : ℕ} (f : Fin d → Q) (hf : Subgroup.closure (Set.range f)=⊤)
    (L : LiftFamily π K) :
    Subgroup.closure ((K : Set E)∪Set.range (selectedLift π K f L))=L.val := by
  let C := Subgroup.closure ((K : Set E)∪Set.range (selectedLift π K f L))
  have hCL : C≤L.val := by
    apply (Subgroup.closure_le _).mpr
    rintro x (hx | ⟨i,rfl⟩)
    · have hh : x∈L.val⊓π.ker := by rw [L.property.2]; exact hx
      exact hh.1
    · exact selectedLift_mem π K f L i
  have hKC : K≤C := fun x hx => Subgroup.subset_closure (Or.inl hx)
  have hmap : C.map π=⊤ := by
    apply top_unique
    rw [←hf]
    apply (Subgroup.closure_le _).mpr
    rintro q ⟨i,rfl⟩
    exact ⟨selectedLift π K f L i,
      Subgroup.subset_closure (Or.inr ⟨i,rfl⟩),selectedLift_map π K f L i⟩
  apply le_antisymm hCL
  intro x hx
  have hh : π x∈C.map π := by rw [hmap]; exact Subgroup.mem_top _
  obtain ⟨y,hy,hyx⟩ := hh
  have hxy : x*y⁻¹∈L.val⊓π.ker := by
    constructor
    · exact L.val.mul_mem hx (L.val.inv_mem (hCL hy))
    · change π (x*y⁻¹)=1
      rw [map_mul,map_inv,hyx,mul_inv_cancel]
  have hxyK : x*y⁻¹∈K := by rw [←L.property.2]; exact hxy
  have hm := C.mul_mem (hKC hxyK) hy
  simpa only [mul_assoc,inv_mul_cancel,mul_one] using hm

private def baseline (π : E →* Q) (hπ : Function.Surjective π)
    {d : ℕ} (f : Fin d → Q) (i : Fin d) : E := Classical.choose (hπ (f i))

private theorem baseline_map (π : E →* Q) (hπ : Function.Surjective π)
    {d : ℕ} (f : Fin d → Q) (i : Fin d) :
    π (baseline π hπ f i)=f i := Classical.choose_spec (hπ (f i))

private def code (π : E →* Q) (hπ : Function.Surjective π) (K : Subgroup E)
    {d : ℕ} (f : Fin d → Q) (L : LiftFamily π K) : Fin d → π.ker := fun i =>
  ⟨(baseline π hπ f i)⁻¹*selectedLift π K f L i,by
    change π ((baseline π hπ f i)⁻¹*selectedLift π K f L i)=1
    rw [map_mul,map_inv,baseline_map,selectedLift_map,inv_mul_cancel]⟩

private theorem code_injective (π : E →* Q) (hπ : Function.Surjective π)
    (K : Subgroup E) {d : ℕ} (f : Fin d → Q)
    (hf : Subgroup.closure (Set.range f)=⊤) :
    Function.Injective (code π hπ K f) := by
  intro L M h
  have ht : selectedLift π K f L=selectedLift π K f M := by
    funext i
    have hh := congrArg (fun a : π.ker => (a : E)) (congrFun h i)
    change (baseline π hπ f i)⁻¹*selectedLift π K f L i=
      (baseline π hπ f i)⁻¹*selectedLift π K f M i at hh
    exact mul_left_cancel hh
  apply Subtype.ext
  rw [←closure_kernel_union_lifts π K f hf L,←closure_kernel_union_lifts π K f hf M,ht]

/-- At fixed image and literal kernel intersection, all subgroup lifts cost
at most |ker π|^d. The extension need not split; K need not be normal in E. -/
theorem card_liftFamily_le [Finite E] (π : E →* Q)
    (hπ : Function.Surjective π) (K : Subgroup E)
    {d : ℕ} (f : Fin d → Q) (hf : Subgroup.closure (Set.range f)=⊤) :
    Nat.card (LiftFamily π K) ≤ (Nat.card π.ker)^d := by
  have hh := Nat.card_le_card_of_injective (code π hπ K f) (code_injective π hπ K f hf)
  simpa only [Nat.card_fun,Nat.card_fin] using hh

end SymmetricSubgroupAsymptotics.FiniteExtensionSubgroupLiftCount
