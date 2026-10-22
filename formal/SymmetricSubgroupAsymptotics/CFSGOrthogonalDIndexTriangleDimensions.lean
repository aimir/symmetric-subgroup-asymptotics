import SymmetricSubgroupAsymptotics.CFSGOrthogonalDIndexSingularTriangle

/-! Exact image and rank-nullity identities for the actual singular
triangle space. They are pure linear algebra with no component premise. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGOrthogonalDIndexTriangleDimensions
open CFSGOrthogonalDIndexSingularTriangle
variable {K : Type*} [Field K] {V : Type*} [AddCommGroup V] [Module K V]

theorem sumHom_range (P L M : Submodule K V) :
    (sumHom P L M).range = P ⊔ L ⊔ M := by
  ext w
  constructor
  · rintro ⟨⟨x, y, z⟩, rfl⟩
    change (x : V) + (y : V) + (z : V) ∈ P ⊔ L ⊔ M
    exact Submodule.mem_sup.mpr
      ⟨(x : V) + (y : V), Submodule.mem_sup.mpr ⟨x, x.property, y, y.property, rfl⟩,
        z, z.property, rfl⟩
  · intro hw
    obtain ⟨xy, hxy, z, hz, he⟩ := Submodule.mem_sup.mp hw
    obtain ⟨x, hx, y, hy, hxy⟩ := Submodule.mem_sup.mp hxy
    refine ⟨(⟨x, hx⟩, (⟨y, hy⟩, ⟨z, hz⟩)), ?_⟩
    change x + y + z = w
    exact (congrArg (fun t => t + z) hxy).trans he

theorem triangleY_range (P L M : Submodule K V) :
    (triangleY P L M).range = L ⊓ (P ⊔ M) := by
  ext y
  constructor
  · rintro ⟨w, rfl⟩
    refine ⟨w.val.2.1.property, ?_⟩
    refine Submodule.mem_sup.mpr
      ⟨-(w.val.1 : V), P.neg_mem w.val.1.property,
        -(w.val.2.2 : V), M.neg_mem w.val.2.2.property, ?_⟩
    have h := triangle_sum P L M w
    change -(w.val.1 : V) + -(w.val.2.2 : V) = (w.val.2.1 : V)
    have hy : (w.val.2.1 : V) = -((w.val.1 : V) + (w.val.2.2 : V)) := by
      apply eq_neg_iff_add_eq_zero.mpr
      calc
        (w.val.2.1 : V) + ((w.val.1 : V) + (w.val.2.2 : V)) =
            (w.val.1 : V) + (w.val.2.1 : V) + (w.val.2.2 : V) := by abel
        _ = 0 := h
    calc
      -(w.val.1 : V) + -(w.val.2.2 : V) =
          -((w.val.1 : V) + (w.val.2.2 : V)) := by abel
      _ = (w.val.2.1 : V) := hy.symm
  · rintro ⟨hy, hpm⟩
    obtain ⟨p, hp, m, hm, he⟩ := Submodule.mem_sup.mp hpm
    have hz : -p + y + -m = 0 := by rw [← he]; abel
    let w : triangleSpace P L M :=
      ⟨(⟨-p, P.neg_mem hp⟩, (⟨y, hy⟩, ⟨-m, M.neg_mem hm⟩)), hz⟩
    exact ⟨w, rfl⟩

theorem triangleSpace_finrank [FiniteDimensional K V] (P L M : Submodule K V) :
    Module.finrank K (triangleSpace P L M) + Module.finrank K ↥(P ⊔ L ⊔ M) =
      Module.finrank K P + Module.finrank K L + Module.finrank K M := by
  have h := LinearMap.finrank_range_add_finrank_ker (sumHom P L M)
  rw [sumHom_range] at h
  simpa [triangleSpace, Module.finrank_prod, add_assoc, add_comm, add_left_comm] using h

end SymmetricSubgroupAsymptotics.CFSGOrthogonalDIndexTriangleDimensions
