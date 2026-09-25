import SymmetricSubgroupAsymptotics.FusionPhysicalCount
import Mathlib.GroupTheory.Perm.Finite

/-!
# Extracting the complete model from an actual distinguished orbit

Every permutation subgroup preserving the literal original orbit block is
pulled back through the faithful disjoint action. The first projection is
the actual induced action, while the second retains the whole complement.
-/

set_option autoImplicit false
noncomputable section

namespace SymmetricSubgroupAsymptotics

variable {Ω Z : Type*} (U : Subgroup (Equiv.Perm Ω))

/-- The unrestricted two-block pullback of an actual physical subgroup. -/
def fusionPhysicalBlockPullback (K : Subgroup (Equiv.Perm (Ω ⊕ Z))) :
    Subgroup (Equiv.Perm Ω × Equiv.Perm Z) :=
  K.comap (Equiv.Perm.sumCongrHom Ω Z)

/-- The deleted model retains both the original orbit action and the
entire complementary permutation group in one actual subgroup. -/
def fusionDeletedModel (K : Subgroup (Equiv.Perm (Ω ⊕ Z))) :
    Subgroup (U × Equiv.Perm Z) := K.comap (fusionOrbitAction U)

/-- Intrinsic block preservation and the actual first restriction image
place the whole physical subgroup inside the original product action. -/
theorem fusionOrbitAction_covers [Finite Ω] [Finite Z]
    (K : Subgroup (Equiv.Perm (Ω ⊕ Z)))
    (hblock : ∀ k ∈ K, Set.MapsTo k (Set.range (Sum.inl : Ω → Ω ⊕ Z))
      (Set.range (Sum.inl : Ω → Ω ⊕ Z)))
    (hprojection : (fusionPhysicalBlockPullback K).map
      (MonoidHom.fst (Equiv.Perm Ω) (Equiv.Perm Z))=U) :
    K ≤ (fusionOrbitAction U).range := by
  intro k hk
  obtain ⟨⟨u,z⟩,he⟩ := Equiv.Perm.mem_sumCongrHom_range_of_perm_mapsTo_inl (hblock k hk)
  have hu : u∈U := by
    rw [← hprojection]
    exact ⟨(u,z),by change Equiv.Perm.sumCongrHom Ω Z (u,z)∈K; rw [he]; exact hk,rfl⟩
  exact ⟨(⟨u,hu⟩,z),he⟩

/-- Reconstruction is literal equality of the original physical subgroup. -/
theorem fusionDeletedModel_recovers [Finite Ω] [Finite Z]
    (K : Subgroup (Equiv.Perm (Ω ⊕ Z)))
    (hblock : ∀ k ∈ K, Set.MapsTo k (Set.range (Sum.inl : Ω → Ω ⊕ Z))
      (Set.range (Sum.inl : Ω → Ω ⊕ Z)))
    (hprojection : (fusionPhysicalBlockPullback K).map
      (MonoidHom.fst (Equiv.Perm Ω) (Equiv.Perm Z))=U) :
    (fusionDeletedModel U K).map (fusionOrbitAction U)=K :=
  Subgroup.map_comap_eq_self (fusionOrbitAction_covers U K hblock hprojection)

/-- The deletion uses the full original orbit projection, not a smaller
quotient action or an independently enlarged complement. -/
theorem fusionDeletedModel_full
    (K : Subgroup (Equiv.Perm (Ω ⊕ Z)))
    (hprojection : (fusionPhysicalBlockPullback K).map
      (MonoidHom.fst (Equiv.Perm Ω) (Equiv.Perm Z))=U) :
    (fusionDeletedModel U K).map (MonoidHom.fst U (Equiv.Perm Z))=⊤ := by
  apply top_unique
  intro u _
  have hu : (u : Equiv.Perm Ω)∈(fusionPhysicalBlockPullback K).map
      (MonoidHom.fst (Equiv.Perm Ω) (Equiv.Perm Z)) := by rw [hprojection]; exact u.2
  obtain ⟨⟨v,z⟩,hv,he⟩ := hu
  change v=(u : Equiv.Perm Ω) at he
  subst v
  exact ⟨(u,z),hv,rfl⟩

/-- An actual orbit is automatically invariant under every original group
element; this supplies the preservation premise above. -/
theorem fusionOrbit_block_preserved
    (K : Subgroup (Equiv.Perm (Ω ⊕ Z))) (x : Ω ⊕ Z)
    (hO : MulAction.orbit K x=Set.range (Sum.inl : Ω → Ω ⊕ Z)) :
    ∀ k ∈ K, Set.MapsTo k (Set.range (Sum.inl : Ω → Ω ⊕ Z))
      (Set.range (Sum.inl : Ω → Ω ⊕ Z)) := by
  intro k hk
  rw [← hO]
  exact MulAction.mapsTo_smul_orbit (⟨k,hk⟩ : K) x

/-- An intrinsic original physical subgroup enters the counted family via
its actual complete model. Survival is tested on exactly that model. -/
theorem fusionDeletedModel_mem_family [Finite Ω] [Finite Z]
    (K : Subgroup (Equiv.Perm (Ω ⊕ Z)))
    (hblock : ∀ k ∈ K, Set.MapsTo k (Set.range (Sum.inl : Ω → Ω ⊕ Z))
      (Set.range (Sum.inl : Ω → Ω ⊕ Z)))
    (hprojection : (fusionPhysicalBlockPullback K).map
      (MonoidHom.fst (Equiv.Perm Ω) (Equiv.Perm Z))=U)
    (P : Subgroup (U × Equiv.Perm Z) → Prop) (hP : P (fusionDeletedModel U K)) :
    K ∈ FusionOrbitFamily U (FusionAcceptedOrbitPredicate U P) := by
  have hm : FusionOrbitModel U (FusionAcceptedOrbitPredicate U P) K :=
    ⟨⟨fusionDeletedModel U K,fusionDeletedModel_full U K hprojection,hP⟩,
      fusionDeletedModel_recovers U K hblock hprojection⟩
  exact ⟨(1,⟨K,hm⟩),by simp⟩

end SymmetricSubgroupAsymptotics
