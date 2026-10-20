import SymmetricSubgroupAsymptotics.NormalGeneratorTypeSharing

/-! Normal generators lift without extra positions when the original
kernel intersection is forced by the selected normal image. The condition
may hold only outside one distinguished normal subgroup; unlike a global
normal cover, it need not hold for every nontrivial normal subgroup. -/

set_option autoImplicit false
noncomputable section
open scoped Classical

namespace SymmetricSubgroupAsymptotics

theorem normal_generating_tuple_of_forced_kernel_intersection
    {G Q : Type} [Group G] [Group Q]
    (pi : G →* Q) (hpi : Function.Surjective pi)
    (N : Subgroup G) [N.Normal] {t : ℕ}
    (x : Fin t → Q) (hx : Subgroup.normalClosure (Set.range x) = N.map pi)
    (hforce : ∀ L : Subgroup G, L.Normal → L.map pi = N.map pi →
      pi.ker ⊓ N ≤ L) :
    ∃ y : Fin t → G, Subgroup.normalClosure (Set.range y) = N := by
  have hlift : ∀ i, ∃ y : G, y ∈ N ∧ pi y = x i := by
    intro i
    have hxi : x i ∈ N.map pi := by
      rw [← hx]
      exact Subgroup.subset_normalClosure (Set.mem_range_self i)
    exact hxi
  choose y hy hpiy using hlift
  let L := Subgroup.normalClosure (Set.range y)
  have hLN : L ≤ N := by
    apply Subgroup.normalClosure_le_normal
    rintro _ ⟨i, rfl⟩
    exact hy i
  have himage : pi '' Set.range y = Set.range x := by
    ext q
    constructor
    · rintro ⟨_, ⟨i, rfl⟩, rfl⟩
      exact ⟨i, (hpiy i).symm⟩
    · rintro ⟨i, rfl⟩
      exact ⟨y i, Set.mem_range_self i, hpiy i⟩
  have hmap : L.map pi = N.map pi := by
    dsimp [L]
    rw [Subgroup.map_normalClosure _ _ hpi, himage]
    exact hx
  have hker := hforce L (inferInstance : L.Normal) hmap
  refine ⟨y, le_antisymm hLN ?_⟩
  intro n hn
  have him : pi n ∈ L.map pi := by
    rw [hmap]
    exact ⟨n, hn, rfl⟩
  obtain ⟨l, hl, hln⟩ := him
  have hdiff : n * l⁻¹ ∈ pi.ker ⊓ N := by
    refine ⟨?_, N.mul_mem hn (N.inv_mem (hLN hl))⟩
    apply MonoidHom.mem_ker.mpr
    rw [map_mul, map_inv, hln, mul_inv_cancel]
  have hprod := L.mul_mem (hker hdiff) hl
  simpa only [inv_mul_cancel_right] using hprod

theorem normalGen_le_of_forced_kernel_intersection
    {G Q : Type} [Group G] [Group Q] [Finite G]
    (pi : G →* Q) (hpi : Function.Surjective pi)
    (N : Subgroup G) [N.Normal] {t : ℕ}
    (himage : MarkedC4.normalGen (N.map pi) ≤ t)
    (hforce : ∀ L : Subgroup G, L.Normal → L.map pi = N.map pi →
      pi.ker ⊓ N ≤ L) :
    MarkedC4.normalGen N ≤ t := by
  letI : Finite Q := Finite.of_surjective pi hpi
  letI : (N.map pi).Normal := (inferInstance : N.Normal).map pi hpi
  obtain ⟨x, hx⟩ := exists_normal_generating_tuple_of_normalGen_le (N.map pi) himage
  obtain ⟨y, hy⟩ := normal_generating_tuple_of_forced_kernel_intersection
    pi hpi N x hx hforce
  exact normalGen_le_of_fin_tuple y hy

/-- A kernel cover may be needed only for normal subgroups not contained
in `E`. Equality of the actual images preserves that noncontainment. -/
theorem normalGen_le_of_kernel_cover_outside
    {G Q : Type} [Group G] [Group Q] [Finite G]
    (pi : G →* Q) (hpi : Function.Surjective pi)
    (E : Subgroup G) (hkerE : pi.ker ≤ E)
    (hcover : ∀ L : Subgroup G, L.Normal → ¬ L ≤ E → pi.ker ≤ L)
    (N : Subgroup G) [N.Normal] (hNE : ¬ N ≤ E) {t : ℕ}
    (himage : MarkedC4.normalGen (N.map pi) ≤ t) :
    MarkedC4.normalGen N ≤ t := by
  apply normalGen_le_of_forced_kernel_intersection pi hpi N himage
  intro L hL hmap
  apply inf_le_left.trans
  apply hcover L hL
  intro hLE
  apply hNE
  calc
    N ≤ (N.map pi).comap pi := Subgroup.le_comap_map pi N
    _ = (L.map pi).comap pi := by rw [hmap]
    _ ≤ (E.map pi).comap pi := Subgroup.comap_mono (Subgroup.map_mono hLE)
    _ = E := Subgroup.comap_map_eq_self hkerE

end SymmetricSubgroupAsymptotics

end
