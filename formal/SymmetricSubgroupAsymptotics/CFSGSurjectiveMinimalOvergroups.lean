import Mathlib.Algebra.Group.Subgroup.Ker

/-! Minimal overgroups descend through a surjection whose kernel lies
in the lower subgroup. The same correspondence transports an actual
exhaustive family and preserves its distinct labels. These are ordinary
subgroup map/comap arguments, with no simplicity or model premise. -/
set_option autoImplicit false
set_option Elab.async false
namespace SymmetricSubgroupAsymptotics.CFSGSurjectiveMinimalOvergroups
variable {G Q : Type*} [Group G] [Group Q] (f : G →* Q)

theorem map_lt_map_of_kernel_le {B P : Subgroup G}
    (hker : f.ker ≤ B) (hBP : B < P) : B.map f < P.map f := by
  refine lt_iff_le_not_ge.mpr ⟨Subgroup.map_mono hBP.le, ?_⟩
  intro h
  have hPB := Subgroup.map_le_map_iff.mp h
  rw [sup_eq_left.mpr hker] at hPB
  exact hBP.not_ge hPB

theorem map_minimal_overgroup (hf : Function.Surjective f)
    {B P : Subgroup G} (hker : f.ker ≤ B) (hBP : B < P)
    (hmin : ∀ H : Subgroup G, B < H → H ≤ P → H = P) :
    ∀ H : Subgroup Q, B.map f < H → H ≤ P.map f → H = P.map f := by
  intro H hBH hHP
  have hBC : B < H.comap f := by
    have h := (Subgroup.comap_lt_comap_of_surjective hf).mpr hBH
    simpa only [Subgroup.comap_map_eq_self hker] using h
  have hCP : H.comap f ≤ P := by
    have h := Subgroup.comap_mono (f := f) hHP
    simpa only [Subgroup.comap_map_eq_self (hker.trans hBP.le)] using h
  have he := congrArg (fun S : Subgroup G => S.map f) (hmin _ hBC hCP)
  simpa only [Subgroup.map_comap_eq_self_of_surjective hf] using he

theorem comap_strict_overgroup (hf : Function.Surjective f)
    {B : Subgroup G} (hker : f.ker ≤ B) {P : Subgroup Q}
    (hBP : B.map f < P) : B < P.comap f := by
  have h := (Subgroup.comap_lt_comap_of_surjective hf).mpr hBP
  simpa only [Subgroup.comap_map_eq_self hker] using h

theorem comap_minimal_overgroup {B : Subgroup G} (hker : f.ker ≤ B) {P : Subgroup Q}
    (hmin : ∀ H : Subgroup Q, B.map f < H → H ≤ P → H = P) :
    ∀ H : Subgroup G, B < H → H ≤ P.comap f → H = P.comap f := by
  intro H hBH hHP
  have hmap := hmin (H.map f) (map_lt_map_of_kernel_le f hker hBH)
    (Subgroup.map_le_iff_le_comap.mpr hHP)
  have he := congrArg (fun S : Subgroup Q => S.comap f) hmap
  simpa only [Subgroup.comap_map_eq_self (hker.trans hBH.le)] using he

theorem minimal_overgroup_family_surjective (hf : Function.Surjective f)
    {B : Subgroup G} (hker : f.ker ≤ B) {I : Type*} (P : I → Subgroup G)
    (hcover : ∀ H : Subgroup G, B < H →
      (∀ M : Subgroup G, B < M → M ≤ H → M = H) → ∃ i, H = P i)
    (H : Subgroup Q) (hBH : B.map f < H)
    (hmin : ∀ M : Subgroup Q, B.map f < M → M ≤ H → M = H) :
    ∃ i, H = (P i).map f := by
  obtain ⟨i, hi⟩ := hcover (H.comap f) (comap_strict_overgroup f hf hker hBH)
    (comap_minimal_overgroup f hker hmin)
  refine ⟨i, ?_⟩
  calc
    H = (H.comap f).map f := (Subgroup.map_comap_eq_self_of_surjective hf H).symm
    _ = (P i).map f := congrArg (fun S : Subgroup G => S.map f) hi

theorem map_family_injective {B : Subgroup G} (hker : f.ker ≤ B)
    {I : Type*} (P : I → Subgroup G) (hBP : ∀ i, B ≤ P i)
    (hinj : Function.Injective P) : Function.Injective (fun i => (P i).map f) := by
  intro i j he
  apply hinj
  exact Subgroup.map_injective_of_ker_le f (hker.trans (hBP i))
    (hker.trans (hBP j)) he

end SymmetricSubgroupAsymptotics.CFSGSurjectiveMinimalOvergroups
