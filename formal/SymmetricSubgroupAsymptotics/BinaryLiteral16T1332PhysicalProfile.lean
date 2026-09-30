import SymmetricSubgroupAsymptotics.BinaryCarrierParameterProfiles
import SymmetricSubgroupAsymptotics.BinarySelectedCatalogueModel16T1332

/-!
# The literal 16T1332 carrier as an original physical profile

The selected split model is already one of the twelve original carrier
colors.  This file records its exact one-occurrence profile in the
`(R,a,T)=(0,0,2)` bin.  The point chart is literal, and the final theorem
transports the certificate through the same conjugacy retained by the
degree-sixteen catalogue owner.
-/

set_option autoImplicit false
noncomputable section
open scoped Classical Pointwise

namespace SymmetricSubgroupAsymptotics.BinaryLiteral16T1332PhysicalProfile

open SymmetricSubgroupAsymptotics
open BinaryCarrierOriginalCyclicFourHall
open BinaryCarrierMasterWords16
open BinaryCarrierParameterProfiles

/-- There is no critical part. -/
def critical : CriticalProfile := ⟨0,0,0,0⟩

/-- The unique occupied noncritical color is the literal degree-sixteen
16T1332 action. -/
def carrierMultiplicity : Target → ℕ
  | some (.degree16 .t1332) => 1
  | _ => 0

theorem critical_mem : critical ∈ criticalProfiles 0 := by
  simp [critical,CriticalProfile.rank]

theorem carrier_parameters :
    carrierMultiplicity none=0 ∧
      BinaryCarrierOriginalActions.scale (fun t => carrierMultiplicity (some t))=2 := by
  constructor
  · rfl
  · decide +kernel

def index : BinaryCarrierParameterProfiles.ProfileIndex 0 0 2 :=
  ⟨⟨critical,critical_mem⟩,
    ⟨carrierMultiplicity,
      (mem_profilesAtParameters 0 2 carrierMultiplicity).mpr carrier_parameters⟩⟩

abbrev multiplicity : CriticalActionKind ⊕ Target → ℕ := fun i => match i with
  | Sum.inl _ => 0
  | Sum.inr (some (.degree16 .t1332)) => 1
  | Sum.inr _ => 0

abbrev pointFamily : CriticalActionKind ⊕ Target → Type :=
  BinaryCarrierMixedProfile.points points

abbrev actionFamily : (i : CriticalActionKind ⊕ Target) →
    Subgroup (Equiv.Perm (pointFamily i)) :=
  BinaryCarrierMixedProfile.action points action

abbrev Original := BinarySelectedCatalogue16T1332.Original

abbrev ModelPoints := OrbitProfilePoints pointFamily multiplicity

def modelPoint (x : Fin 16) : ModelPoints :=
  ⟨Sum.inr (some (.degree16 .t1332)),0,x⟩

def chartFun : ModelPoints → Fin 16
  | ⟨Sum.inl .c2,j,_⟩ => Fin.elim0 j
  | ⟨Sum.inl .v4,j,_⟩ => Fin.elim0 j
  | ⟨Sum.inl .d8,j,_⟩ => Fin.elim0 j
  | ⟨Sum.inl .e8,j,_⟩ => Fin.elim0 j
  | ⟨Sum.inr none,j,_⟩ => Fin.elim0 j
  | ⟨Sum.inr (some (.degree8 .t18)),j,_⟩ => Fin.elim0 j
  | ⟨Sum.inr (some (.degree8 .t26)),j,_⟩ => Fin.elim0 j
  | ⟨Sum.inr (some (.degree8 .t27)),j,_⟩ => Fin.elim0 j
  | ⟨Sum.inr (some (.degree8 .t28)),j,_⟩ => Fin.elim0 j
  | ⟨Sum.inr (some (.degree8 .t29)),j,_⟩ => Fin.elim0 j
  | ⟨Sum.inr (some (.degree8 .t31)),j,_⟩ => Fin.elim0 j
  | ⟨Sum.inr (some (.degree8 .t35)),j,_⟩ => Fin.elim0 j
  | ⟨Sum.inr (some (.degree16 .t1082)),j,_⟩ => Fin.elim0 j
  | ⟨Sum.inr (some (.degree16 .t1083)),j,_⟩ => Fin.elim0 j
  | ⟨Sum.inr (some (.degree16 .t1084)),j,_⟩ => Fin.elim0 j
  | ⟨Sum.inr (some (.degree16 .t1332)),_,x⟩ => x
  | ⟨Sum.inr (some (.degree16 .t1547)),j,_⟩ => Fin.elim0 j

def chart : ModelPoints ≃ Fin 16 where
  toFun := chartFun
  invFun := modelPoint
  left_inv := by
    rintro ⟨i,j,x⟩
    rcases i with i|t
    · rcases i with _|_|_|_ <;> exact Fin.elim0 j
    · rcases t with _|t
      · exact Fin.elim0 j
      · rcases t with t|m
        · rcases t with _|_|_|_|_|_|_ <;> exact Fin.elim0 j
        · rcases m with _|_|_|_|_
          · exact Fin.elim0 j
          · exact Fin.elim0 j
          · exact Fin.elim0 j
          · fin_cases j
            rfl
          · exact Fin.elim0 j
  right_inv := fun _ => rfl

@[simp] theorem chart_modelPoint (x : Fin 16) : chart (modelPoint x)=x := rfl

theorem indexed_multiplicity :
    BinaryCarrierParameterProfiles.profileMultiplicity 0 0 2 index = multiplicity := by
  funext i
  rcases i with i|t
  · rcases i with _|_|_|_ <;> rfl
  · rcases t with _|t
    · rfl
    · rcases t with t|m
      · rcases t with _|_|_|_|_|_|_ <;> rfl
      · rcases m with _|_|_|_|_ <;> rfl

/-- On the unique occupied block, profile fullness is exactly membership
in the original 16T1332 subgroup. -/
theorem carrier_full : OrbitProfileFullOn actionFamily chart Original := by
  constructor
  · intro h i j
    rcases i with i|t
    · rcases i with _|_|_|_ <;> exact Fin.elim0 j
    · rcases t with _|t
      · exact Fin.elim0 j
      · rcases t with t|m
        · rcases t with _|_|_|_|_|_|_ <;> exact Fin.elim0 j
        · rcases m with _|_|_|_|_
          · exact Fin.elim0 j
          · exact Fin.elim0 j
          · exact Fin.elim0 j
          · exact ⟨h,fun _ => rfl⟩
          · exact Fin.elim0 j
  · intro i j u
    rcases i with i|t
    · rcases i with _|_|_|_ <;> exact Fin.elim0 j
    · rcases t with _|t
      · exact Fin.elim0 j
      · rcases t with t|m
        · rcases t with _|_|_|_|_|_|_ <;> exact Fin.elim0 j
        · rcases m with _|_|_|_|_
          · exact Fin.elim0 j
          · exact Fin.elim0 j
          · exact Fin.elim0 j
          · exact ⟨u,fun _ => rfl⟩
          · exact Fin.elim0 j

private theorem assembledWitnessOfMultiplicityEq
    {m : CriticalActionKind ⊕ Target → ℕ} (hm : m=multiplicity) :
    ∃ e : OrbitProfilePoints pointFamily m ≃ Fin 16, ∃ K,
      OrbitProfileFull (m := m) actionFamily 1 K ∧ relabelSubgroup e K=Original := by
  subst m
  let K := relabelSubgroup chart.symm Original
  refine ⟨chart,K,?_,?_⟩
  · apply (orbitProfileFullOn_iff actionFamily 1 K).mp
    simpa only [Equiv.self_trans_symm] using carrier_full.relabel chart.symm
  · exact relabelSubgroup_symm chart.symm _

/-- The literal carrier belongs to the exact parameter bin used by the
complete carrier-mixture estimate. -/
def carrierPhysicalFamily :
    BinaryCarrierParameterProfiles.PhysicalFamily 0 0 2 (Fin 16) := by
  refine ⟨Original,?_⟩
  refine ⟨index,?_⟩
  simpa only [BinaryCarrierParameterProfiles.profilePredicate] using
    assembledWitnessOfMultiplicityEq indexed_multiplicity

/-- Conjugating the selected carrier changes only its physical labels and
therefore stays in the same original-action profile bin. -/
def transportedPhysicalFamily
    {U : Subgroup (Equiv.Perm (Fin 16))} (g : Equiv.Perm (Fin 16))
    (hg : MulAut.conj g • U=Original) :
    BinaryCarrierParameterProfiles.PhysicalFamily 0 0 2 (Fin 16) := by
  change relabelSubgroup g U=Original at hg
  refine ⟨U,?_⟩
  obtain ⟨e,K,hK,he⟩ := assembledWitnessOfMultiplicityEq indexed_multiplicity
  refine ⟨index,e.trans g.symm,K,?_,?_⟩
  · simpa only [BinaryCarrierParameterProfiles.profilePredicate] using hK
  · rw [← relabelSubgroup_trans,he,← hg]
    exact relabelSubgroup_symm g U

end SymmetricSubgroupAsymptotics.BinaryLiteral16T1332PhysicalProfile
