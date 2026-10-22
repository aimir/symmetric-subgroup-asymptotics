import SymmetricSubgroupAsymptotics.CFSGSymplecticRootPointGeometry
import SymmetricSubgroupAsymptotics.CFSGSubgroupFamilyFaithfulness

/-! In odd characteristic the actual projective automorphism group
acts faithfully on the original projective points, through literal
collineations. Simplicity is only used for faithfulness of the abstract
subgroup-family action, not as a recognition premise. -/
set_option autoImplicit false
noncomputable section
open scoped LinearAlgebra.Projectivization
namespace SymmetricSubgroupAsymptotics.CFSGSymplecticPointRootLabels
open CFSGSymplecticSerreMatrices CFSGSymplecticTransvectionGeometry
variable {K : Type} [Field K]

theorem label_ne_bot (r : ℕ) (hr : 0 < r) (p : Points (K := K) r) :
    label r hr p ≠ ⊥ := by
  intro he
  let R := projectiveNaturalRootHom r hr p.rep
  have hm : R (Multiplicative.ofAdd 1) ∈ label r hr p := ⟨_, rfl⟩
  rw [he] at hm
  have heq := projectiveNaturalRootHom_injective r hr p.rep p.rep_nonzero
    ((Subgroup.mem_bot.mp hm).trans R.map_one.symm)
  exact one_ne_zero (congrArg Multiplicative.toAdd heq)

theorem label_ne_top (r : ℕ) (hr : 0 < r) (p : Points (K := K) r) :
    label r hr p ≠ ⊤ := by
  intro he
  obtain ⟨w, hw⟩ := exists_pairing_ne_zero (r + 1) p.rep p.rep_nonzero
  have hm : projectiveNaturalRootHom r hr w (Multiplicative.ofAdd 1) ∈ label r hr p := by
    rw [he]; trivial
  obtain ⟨a, ha⟩ := hm
  have hc : Commute (projectiveNaturalRootHom r hr p.rep (Multiplicative.ofAdd 1))
      (projectiveNaturalRootHom r hr w (Multiplicative.ofAdd 1)) := by
    rw [← ha]
    exact (Commute.all (Multiplicative.ofAdd (1 : K)) a).map _
  exact hw ((projectiveNaturalRootElement_commute_iff r hr _ _ (1 : K) 1
    one_ne_zero one_ne_zero).mp hc)

variable [Finite K]

def oddPointHom (p r : ℕ) [Fact p.Prime] [CharP K p]
    (hr : 0 < r) (htwo : (2 : K) ≠ 0) :
    MulAut (elementaryProjective K (r + 1)) →* Equiv.Perm (Points (K := K) r) :=
  CFSGSubgroupFamilyPermutation.permutationHom (label r hr) (label_injective r hr)
    (odd_stable p r hr htwo)

theorem oddPointHom_label (p r : ℕ) [Fact p.Prime] [CharP K p]
    (hr : 0 < r) (htwo : (2 : K) ≠ 0)
    (f : MulAut (elementaryProjective K (r + 1))) (x : Points (K := K) r) :
    label r hr (oddPointHom p r hr htwo f x) = (label r hr x).map f.toMonoidHom :=
  CFSGSubgroupFamilyPermutation.label_permutation (label r hr) (label_injective r hr)
    (odd_stable p r hr htwo) f x

theorem oddPointHom_injective (p r : ℕ) [Fact p.Prime] [CharP K p]
    (hr : 0 < r) (htwo : (2 : K) ≠ 0)
    [IsSimpleGroup (elementaryProjective K (r + 1))] :
    Function.Injective (oddPointHom p r hr htwo) := by
  let v : Index (r + 1) → K := Pi.single (Sum.inl 0) 1
  have hv : v ≠ 0 := by
    intro he
    have hh := congrFun he (Sum.inl 0)
    simpa [v] using hh
  let x := Projectivization.mk K v hv
  exact CFSGSubgroupFamilyFaithfulness.permutationHom_injective (label r hr)
    (label_injective r hr) (odd_stable p r hr htwo) x (label_ne_bot r hr x)
    (label_ne_top r hr x)

def oddCollineationHom (p r : ℕ) [Fact p.Prime] [CharP K p]
    (hr : 0 < r) (htwo : (2 : K) ≠ 0) :
    MulAut (elementaryProjective K (r + 1)) →*
      CFSGProjectiveFrameCoordinates.collineationGroup (F := K) (n := Index (r + 1)) :=
  (oddPointHom p r hr htwo).codRestrict _ (fun f =>
    collineation_of_label_map r hr f _ (oddPointHom_label p r hr htwo f))

theorem oddCollineationHom_injective (p r : ℕ) [Fact p.Prime] [CharP K p]
    (hr : 0 < r) (htwo : (2 : K) ≠ 0)
    [IsSimpleGroup (elementaryProjective K (r + 1))] :
    Function.Injective (oddCollineationHom p r hr htwo) := by
  intro f g he
  apply oddPointHom_injective p r hr htwo
  exact congrArg Subtype.val he

end SymmetricSubgroupAsymptotics.CFSGSymplecticPointRootLabels
