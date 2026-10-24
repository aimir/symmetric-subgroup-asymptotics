import Mathlib.Algebra.Group.Subgroup.Lattice

/-! A separating family of actual generator overgroups is precisely the
minimal strict overgroup family when every strict overgroup contains one
of those generators. The hypotheses concern literal subgroup membership;
no BN-pair, rank-one presentation, or group recognition is assumed. -/
set_option autoImplicit false
set_option Elab.async false
namespace SymmetricSubgroupAsymptotics.CFSGMinimalOvergroupsOfGenerators
variable {G I : Type*} [Group G]

def generatorOvergroup (B : Subgroup G) (w : I→G) (i : I) : Subgroup G :=
  B⊔Subgroup.closure {w i}

theorem base_lt_generatorOvergroup (B : Subgroup G) (w : I→G)
    (hn : ∀i,w i∉B) (i : I) : B<generatorOvergroup B w i := by
  refine lt_iff_le_not_ge.mpr ⟨le_sup_left,?_⟩
  intro hle
  exact hn i (hle ((show Subgroup.closure {w i}≤generatorOvergroup B w i from le_sup_right)
    (Subgroup.subset_closure (Set.mem_singleton _))))

theorem generatorOvergroup_minimal (B : Subgroup G) (w : I→G)
    (hsep : ∀i j,j≠i→w j∉generatorOvergroup B w i)
    (hextract : ∀H : Subgroup G,B<H→∃j,w j∈H)
    (i : I) (H : Subgroup G) (hBH : B<H) (hHP : H≤generatorOvergroup B w i) :
    H=generatorOvergroup B w i := by
  obtain ⟨j,hj⟩ := hextract H hBH
  have hji : j=i := by
    by_contra hne
    exact hsep i j hne (hHP hj)
  subst j
  apply le_antisymm hHP
  exact sup_le hBH.le ((Subgroup.closure_le _).mpr (Set.singleton_subset_iff.mpr hj))

theorem minimal_overgroup_eq_generatorOvergroup (B : Subgroup G) (w : I→G)
    (hn : ∀i,w i∉B) (hextract : ∀H : Subgroup G,B<H→∃j,w j∈H)
    (H : Subgroup G) (hBH : B<H)
    (hmin : ∀M : Subgroup G,B<M→M≤H→M=H) :
    ∃i,H=generatorOvergroup B w i := by
  obtain ⟨i,hi⟩ := hextract H hBH
  refine ⟨i,(hmin _ (base_lt_generatorOvergroup B w hn i) ?_).symm⟩
  exact sup_le hBH.le ((Subgroup.closure_le _).mpr (Set.singleton_subset_iff.mpr hi))

theorem generatorOvergroup_injective (B : Subgroup G) (w : I→G)
    (hsep : ∀i j,j≠i→w j∉generatorOvergroup B w i) :
    Function.Injective (generatorOvergroup B w) := by
  intro i j he
  by_contra hne
  have hj : w j∈generatorOvergroup B w j :=
    (show Subgroup.closure {w j}≤generatorOvergroup B w j from le_sup_right)
      (Subgroup.subset_closure (Set.mem_singleton _))
  exact hsep i j (Ne.symm hne) (he.symm ▸ hj)

end SymmetricSubgroupAsymptotics.CFSGMinimalOvergroupsOfGenerators
