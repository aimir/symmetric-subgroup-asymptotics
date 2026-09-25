import SymmetricSubgroupAsymptotics.BinaryCoordinateSpaces
import Mathlib.Algebra.Field.ZMod

/-! Small basis and orbit witnesses check complete invariant-axis
registries. Every subgroup inclusion is proved from reversible coordinate
charts. Original action generators and their inverses are retained. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace SymmetricSubgroupAsymptotics

variable {G ι : Type*} [Group G] {w d : ℕ}

/-- Coordinate-basis checks on actual generators establish invariance
under the entire original action. -/
def BinaryCoordinateSpace.subrepresentationOfGenerators
    (C : BinaryCoordinateSpace w d)
    (ρ : Representation (ZMod 2) G (Fin w → ZMod 2))
    (generators : ι → G) (hgen : Subgroup.closure (Set.range generators)=⊤)
    (hpos : ∀ i j, ρ (generators i) (C.inclusion (Pi.single j 1))∈C.space)
    (hneg : ∀ i j, ρ (generators i)⁻¹ (C.inclusion (Pi.single j 1))∈C.space) :
    Subrepresentation ρ := by
  have hp : ∀ i, ∀ v∈C.space, ρ (generators i) v∈C.space := by
    intro i
    exact C.le_of_basis_mem (C.space.comap (ρ (generators i))) (hpos i)
  have hn : ∀ i, ∀ v∈C.space, ρ (generators i)⁻¹ v∈C.space := by
    intro i
    exact C.le_of_basis_mem (C.space.comap (ρ (generators i)⁻¹)) (hneg i)
  let S : Subgroup G := {
    carrier := {g | ∀ v, v∈C.space ↔ ρ g v∈C.space}
    one_mem' := by intro v; simp
    mul_mem' := by
      intro a b ha hb v
      simpa only [map_mul,Module.End.mul_apply] using (hb v).trans (ha (ρ b v))
    inv_mem' := by
      intro a ha v
      have h := ha (ρ a⁻¹ v)
      have he : ρ a (ρ a⁻¹ v)=v := by
        change (ρ a*ρ a⁻¹) v=v
        rw [← map_mul,mul_inv_cancel,map_one]
        rfl
      rw [he] at h
      exact h.symm }
  have hS : S=⊤ := by
    apply top_unique
    rw [← hgen]
    apply (Subgroup.closure_le S).mpr
    rintro _ ⟨i,rfl⟩
    intro v
    refine ⟨hp i v,?_⟩
    intro hv
    have h := hn i (ρ (generators i) v) hv
    have he : ρ (generators i)⁻¹ (ρ (generators i) v)=v := by
      change (ρ (generators i)⁻¹*ρ (generators i)) v=v
      rw [← map_mul,inv_mul_cancel,map_one]
      rfl
    rwa [he] at h
  exact ⟨C.space,fun g v hv => (show g∈S by rw [hS]; trivial) v |>.mp hv⟩

/-- A sparse decomposition proves that each new coordinate basis vector
belongs to the old axis plus the actual orbit span of the adjoined point. -/
theorem binaryCoordinate_le_orbit_join {a b : ℕ}
    (A : BinaryCoordinateSpace w a) (B : BinaryCoordinateSpace w b)
    (ρ : Representation (ZMod 2) G (Fin w → ZMod 2)) (v : Fin w → ZMod 2)
    (old : Fin b → Fin a → ZMod 2) (orbit : Fin b → List G)
    (h : ∀ j, B.inclusion (Pi.single j 1)=
      A.inclusion (old j)+((orbit j).map (fun g => ρ g v)).sum) :
    B.space≤A.space⊔binaryOrbitSpan (k := ZMod 2) ρ v := by
  apply B.le_of_basis_mem
  intro j
  rw [h]
  apply (A.space⊔binaryOrbitSpan (k := ZMod 2) ρ v).add_mem
  · exact (show A.space≤A.space⊔binaryOrbitSpan (k := ZMod 2) ρ v from le_sup_left) ⟨old j,rfl⟩
  · apply (show binaryOrbitSpan (k := ZMod 2) ρ v≤A.space⊔binaryOrbitSpan (k := ZMod 2) ρ v from le_sup_right)
    apply (binaryOrbitSpan (k := ZMod 2) ρ v).list_sum_mem
    intro x hx
    obtain ⟨g,hg,rfl⟩ := List.mem_map.mp hx
    exact Submodule.subset_span ⟨g,rfl⟩

/-- Two finite basis containments and sparse orbit witnesses prove the
local equality needed by the complete invariant registry. -/
theorem binaryCoordinate_orbit_join_eq {a b : ℕ}
    (A : BinaryCoordinateSpace w a) (B : BinaryCoordinateSpace w b)
    (ρ : Representation (ZMod 2) G (Fin w → ZMod 2))
    (Bstable : Subrepresentation ρ) (hB : Bstable.toSubmodule=B.space)
    (v : Fin w → ZMod 2)
    (hA : ∀ j, A.inclusion (Pi.single j 1)∈B.space) (hv : v∈B.space)
    (old : Fin b → Fin a → ZMod 2) (orbit : Fin b → List G)
    (h : ∀ j, B.inclusion (Pi.single j 1)=
      A.inclusion (old j)+((orbit j).map (fun g => ρ g v)).sum) :
    B.space=A.space⊔binaryOrbitSpan (k := ZMod 2) ρ v := by
  apply le_antisymm (binaryCoordinate_le_orbit_join A B ρ v old orbit h)
  apply sup_le (A.le_of_basis_mem B.space hA)
  rw [← hB] at hv ⊢
  exact binaryOrbitSpan_le ρ Bstable hv

end SymmetricSubgroupAsymptotics
