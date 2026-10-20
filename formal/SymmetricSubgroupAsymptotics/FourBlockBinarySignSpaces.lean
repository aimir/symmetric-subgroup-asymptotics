import SymmetricSubgroupAsymptotics.BinarySignTernaryPointAction
import SymmetricSubgroupAsymptotics.DihedralNormalGenerators
import SymmetricSubgroupAsymptotics.TernaryFourBlockPermutationGenerators

/-! Actual even and full binary sign spaces and the displayed C4,D8,S4
block complements. The common four-cycle is retained in every model. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped Classical BigOperators

namespace SymmetricSubgroupAsymptotics.FourBlockBinarySignSpaces

open TernaryFourBlockPermutationGenerators BinarySignTernaryLinear

def sumMap : BinaryVector →ₗ[ZMod 2] ZMod 2 where
  toFun v := ∑ i, v i
  map_add' _ _ := Finset.sum_add_distrib
  map_smul' _ _ := by simp only [Finset.smul_sum,Pi.smul_apply,RingHom.id_apply]

def space {R : Type} [Group R] [MulAction R (Fin 4)] (even : Bool) :
    Subrepresentation (CyclicOrbitBinarySignNormalGenerators.permutationRepresentation
      (R := R) (X := Fin 4)) where
  toSubmodule := if even then sumMap.ker else ⊤
  apply_mem_toSubmodule g v hv := by
    cases even
    · exact Submodule.mem_top
    · change (∑ i : Fin 4, v (g⁻¹ • i)) = 0
      change (∑ i : Fin 4, v i) = 0 at hv
      change (∑ i : Fin 4, v ((MulAction.toPermHom R (Fin 4) g⁻¹) i)) = 0
      rw [Equiv.sum_comp (MulAction.toPermHom R (Fin 4) g⁻¹) v]
      exact hv

theorem pair_mem {R : Type} [Group R] [MulAction R (Fin 4)] (even : Bool) (i j : Fin 4) :
    pair i j ∈ (space (R := R) even).toSubmodule := by
  cases even
  · exact Submodule.mem_top
  · change sumMap (Pi.single i 1 + Pi.single j 1) = 0
    rw [map_add]
    simp only [sumMap,LinearMap.coe_mk,AddHom.coe_mk,Fintype.sum_pi_single']
    decide +kernel

def signSeed {R : Type} [Group R] [MulAction R (Fin 4)] (even : Bool) :
    (space (R := R) even).toSubmodule := by
  cases even
  · exact ⟨Pi.single 0 1,Submodule.mem_top⟩
  · exact ⟨pair 0 1,pair_mem true 0 1⟩

def reflection : Equiv.Perm (Fin 4) := Equiv.swap 1 3

abbrev Cyclic := Subgroup.zpowers c
def cyclicGenerator : Cyclic := ⟨c,Subgroup.mem_zpowers c⟩

def dihedralMap : DihedralGroup 4 →* Equiv.Perm (Fin 4) where
  toFun
    | .r i => c^i.val
    | .sr i => reflection*c^i.val
  map_one' := rfl
  map_mul' := by
    rintro (i | i) (j | j) <;>
      apply Equiv.ext <;> intro x <;> revert i j x <;> decide +kernel

abbrev Dihedral := dihedralMap.range
def dihedralRotation : Dihedral := ⟨c,⟨DihedralGroup.r 1,by decide +kernel⟩⟩
def dihedralReflection : Dihedral := ⟨reflection,⟨DihedralGroup.sr 0,by decide +kernel⟩⟩

theorem cyclic_orbit : ∀ i : Fin 4, ∃ n : ℕ, cyclicGenerator^n • 0 = i := by
  intro i
  refine ⟨i.val,?_⟩
  change (c^i.val) 0 = i
  revert i
  decide +kernel

theorem dihedral_orbit : ∀ i : Fin 4, ∃ n : ℕ, dihedralRotation^n • 0 = i := by
  intro i
  refine ⟨i.val,?_⟩
  change (c^i.val) 0 = i
  revert i
  decide +kernel

theorem symmetric_orbit : ∀ i : Fin 4, ∃ n : ℕ, c^n • 0 = i := by
  intro i
  refine ⟨i.val,?_⟩
  change (c^i.val) 0 = i
  revert i
  decide +kernel

theorem cyclic_normalGen (K : Subgroup Cyclic) (hK : K.Normal) : MarkedC4.normalGen K ≤ 1 := by
  letI := hK
  exact CoprimeCyclicQuotientSocles.normalGen_le_one_of_isCyclic K

theorem dihedral_normalGen (K : Subgroup Dihedral) (hK : K.Normal) : MarkedC4.normalGen K ≤ 2 := by
  letI := hK
  obtain ⟨x,hx⟩ := normal_generating_tuples_of_surjective dihedralMap.rangeRestrict
    dihedralMap.rangeRestrict_surjective (DihedralNormalGenerators.normal_generating_pairs 4) K hK
  exact normalGen_le_of_fin_tuple x hx

theorem symmetric_normalGen (K : Subgroup (Equiv.Perm (Fin 4))) (hK : K.Normal) :
    MarkedC4.normalGen K ≤ 1 := by
  letI := hK
  obtain ⟨x,hx⟩ := normal_generating_singletons_of_finite_normal_total
    NaturalFourNormalChains.symmetric_normal_total K hK
  exact normalGen_le_of_fin_tuple x hx

theorem cyclic_mem (K : Subgroup Cyclic) (hc : cyclicGenerator ∈ K) : ∀ r : Cyclic, r ∈ K := by
  intro r
  obtain ⟨n,hn⟩ := Subgroup.mem_zpowers_iff.mp r.2
  have he : cyclicGenerator^n = r := Subtype.ext hn
  rw [← he]
  exact K.zpow_mem hc n

theorem dihedral_mem (K : Subgroup Dihedral)
    (hc : dihedralRotation ∈ K) (hr : dihedralReflection ∈ K) : ∀ r : Dihedral, r ∈ K := by
  intro r
  obtain ⟨g,hg⟩ := r.2
  cases g with
  | r i =>
    have he : dihedralRotation^i.val = r := Subtype.ext hg
    rw [← he]
    exact K.pow_mem hc _
  | sr i =>
    have he : dihedralReflection*dihedralRotation^i.val = r := Subtype.ext hg
    rw [← he]
    exact K.mul_mem hr (K.pow_mem hc _)

theorem symmetric_mem (K : Subgroup (Equiv.Perm (Fin 4)))
    (hc : c ∈ K) (hs : s ∈ K) : ∀ r : Equiv.Perm (Fin 4), r ∈ K := by
  have htop : (⊤ : Subgroup (Equiv.Perm (Fin 4))) ≤ K := by
    rw [← symmetric_generated]
    apply (Subgroup.closure_le _).mpr
    intro r hr
    simp only [Set.mem_insert_iff,Set.mem_singleton_iff] at hr
    rcases hr with rfl | rfl
    · exact hc
    · exact hs
  exact fun r => htop (Subgroup.mem_top r)

end SymmetricSubgroupAsymptotics.FourBlockBinarySignSpaces

end
