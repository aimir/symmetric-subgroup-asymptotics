import SymmetricSubgroupAsymptotics.ModuleGeneratorProjectionSharing

/-! Generator positions can be shared across a nonsplit exact sequence
when its kernel is comparable with every submodule. A submodule inside
the kernel uses the kernel bound. Otherwise it contains the kernel, and
any tuple lifting generators of its nonzero image already generates it.
No splitting or semisimplicity is assumed. -/

set_option autoImplicit false
noncomputable section
open scoped Classical

namespace SymmetricSubgroupAsymptotics
namespace ModuleGeneratedBy

variable {R A M Q : Type} [Ring R]
  [AddCommGroup A] [Module R A]
  [AddCommGroup M] [Module R M]
  [AddCommGroup Q] [Module R Q]

/-- A kernel comparable with every submodule adds no generator positions
to a uniform bound on the quotient and on submodules inside the kernel. -/
theorem uniform_of_kernel_comparison (q : M →ₗ[R] Q) (n : ℕ)
    (hker : ∀ W : Submodule R M, W ≤ q.ker → ModuleGeneratedBy R W n)
    (hquot : ∀ U : Submodule R Q, ModuleGeneratedBy R U n)
    (hcompare : ∀ S : Submodule R M, ¬ S ≤ q.ker → q.ker ≤ S)
    (W : Submodule R M) : ModuleGeneratedBy R W n := by
  by_cases hW : W ≤ q.ker
  · exact hker W hW
  let U := W.map q
  obtain ⟨u, hu⟩ := hquot U
  have hlift : ∀ j : Fin n, ∃ w : W, q w.1 = (u j).1 := by
    intro j
    obtain ⟨w, hw, hqw⟩ := (u j).property
    exact ⟨⟨w, hw⟩, hqw⟩
  choose v hv using hlift
  let P : Submodule R W := Submodule.span R (Set.range v)
  let S : Submodule R M := P.map W.subtype
  have hvS (j : Fin n) : (v j).1 ∈ S :=
    ⟨v j, Submodule.subset_span ⟨j, rfl⟩, rfl⟩
  have hU : U ≤ S.map q := by
    have hspan : Submodule.span R (Set.range u) ≤ (S.map q).comap U.subtype := by
      apply Submodule.span_le.mpr
      rintro _ ⟨j, rfl⟩
      exact ⟨(v j).1, hvS j, hv j⟩
    rw [hu] at hspan
    intro x hx
    exact hspan (show (⟨x, hx⟩ : U) ∈ ⊤ from Submodule.mem_top)
  have hS : ¬ S ≤ q.ker := by
    intro hSK
    apply hW
    intro x hx
    have hqx : q x ∈ S.map q := hU ⟨x, hx, rfl⟩
    obtain ⟨y, hy, hqy⟩ := hqx
    change q x = 0
    rw [← hqy]
    exact hSK hy
  have hKS : q.ker ≤ S := hcompare S hS
  have hWS : W ≤ S := by
    intro x hx
    have hqx : q x ∈ S.map q := hU ⟨x, hx, rfl⟩
    obtain ⟨y, hy, hqy⟩ := hqx
    have hdiff : x - y ∈ q.ker := by
      change q (x - y) = 0
      rw [map_sub, hqy, sub_self]
    have hadd := S.add_mem (hKS hdiff) hy
    simpa only [sub_add_cancel] using hadd
  refine ⟨v, top_unique ?_⟩
  intro x _
  obtain ⟨y, hy, hyx⟩ := hWS x.property
  exact (Subtype.ext hyx : y = x) ▸ hy

/-- Exact-sequence form: the two ends share a uniform generator budget
when every submodule outside the kernel contains the whole kernel. -/
theorem uniform_of_comparable_exact (i : A →ₗ[R] M) (q : M →ₗ[R] Q)
    (hi : Function.Injective i) (hexact : i.range = q.ker) (n : ℕ)
    (hleft : ∀ U : Submodule R A, ModuleGeneratedBy R U n)
    (hright : ∀ U : Submodule R Q, ModuleGeneratedBy R U n)
    (hcompare : ∀ S : Submodule R M, ¬ S ≤ q.ker → q.ker ≤ S)
    (W : Submodule R M) : ModuleGeneratedBy R W n := by
  apply uniform_of_kernel_comparison q n ?_ hright hcompare W
  intro S hS
  let L := S.comap i
  let f : L →ₗ[R] S :=
    { toFun := fun x ↦ ⟨i x.1, x.2⟩
      map_add' _ _ := by apply Subtype.ext; exact map_add i _ _
      map_smul' _ _ := by apply Subtype.ext; exact map_smul i _ _ }
  have hf : Function.Bijective f := by
    constructor
    · intro x y hxy
      apply Subtype.ext
      exact hi (congrArg Subtype.val hxy)
    · intro y
      have hy : y.1 ∈ i.range := by
        rw [hexact]
        exact hS y.property
      obtain ⟨x, hx⟩ := hy
      have hxL : x ∈ L := by
        change i x ∈ S
        rw [hx]
        exact y.property
      exact ⟨⟨x, hxL⟩, Subtype.ext hx⟩
  exact congr (LinearEquiv.ofBijective f hf) (hleft L)

end ModuleGeneratedBy
end SymmetricSubgroupAsymptotics

end
