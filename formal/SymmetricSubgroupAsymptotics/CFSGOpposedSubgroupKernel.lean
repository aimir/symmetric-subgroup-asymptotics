import Mathlib.GroupTheory.Subgroup.Centralizer
import Mathlib.Algebra.Group.Subgroup.Ker

/-! Kernel recognition using actual opposed subgroup images.
If every strict upper overgroup supplies a nontrivial element moved from
U to V, injectivity on U and disjoint image subgroups force the pullback
of the U-image normalizer to be the upper subgroup. A kernel contained
in a subgroup normalizing two generating injective subgroups is central.
No faithfulness on the whole source is assumed by either statement. -/
set_option autoImplicit false
set_option Elab.async false
namespace SymmetricSubgroupAsymptotics.CFSGOpposedSubgroupKernel
variable {G Q : Type*} [Group G] [Group Q]

def normalizerPullback (f : G →* Q) (U : Subgroup G) : Subgroup G :=
  (Subgroup.normalizer (U.map f : Set Q)).comap f

theorem kernel_le_normalizerPullback (f : G →* Q) (U : Subgroup G) :
    f.ker ≤ normalizerPullback f U := by
  intro k hk
  change f k ∈ Subgroup.normalizer (U.map f : Set Q)
  rw [show f k = 1 from hk]
  exact (Subgroup.normalizer (U.map f : Set Q)).one_mem

theorem normalizerPullback_le_upper (f : G →* Q) (U V B : Subgroup G)
    (hB : B ≤ normalizerPullback f U)
    (hdisjoint : U.map f ⊓ V.map f = ⊥)
    (hinjU : Set.InjOn f (U : Set G))
    (hwitness : ∀ L : Subgroup G, B < L → ∃ n ∈ L, ∃ u ∈ U,
      n * u * n⁻¹ ∈ V ∧ n * u * n⁻¹ ≠ 1) :
    normalizerPullback f U ≤ B := by
  by_cases he : normalizerPullback f U = B
  · exact he.le
  have hstrict : B < normalizerPullback f U := lt_of_le_of_ne hB (Ne.symm he)
  obtain ⟨n, hn, u, hu, hv, hne⟩ := hwitness (normalizerPullback f U) hstrict
  have hnorm : f n ∈ Subgroup.normalizer (U.map f : Set Q) := hn
  have hpos : f (n * u * n⁻¹) ∈ U.map f := by
    rw [map_mul, map_mul, map_inv]
    exact (Subgroup.mem_normalizer_iff.mp hnorm (f u)).mp ⟨u, hu, rfl⟩
  have hzero : f (n * u * n⁻¹) = 1 := by
    apply Subgroup.mem_bot.mp
    rw [← hdisjoint]
    exact ⟨hpos, ⟨n * u * n⁻¹, hv, rfl⟩⟩
  have huimage : f u = 1 := by
    have h := congrArg (fun z : Q => (f n)⁻¹ * z * f n) hzero
    simpa only [map_mul, map_inv, mul_assoc, inv_mul_cancel, mul_inv_cancel,
      inv_mul_cancel_left, mul_inv_cancel_left, one_mul, mul_one] using h
  have huone := hinjU hu U.one_mem (huimage.trans (map_one f).symm)
  apply False.elim
  apply hne
  rw [huone, mul_one, mul_inv_cancel]

theorem kernel_le_upper (f : G →* Q) (U V B : Subgroup G)
    (hB : B ≤ normalizerPullback f U)
    (hdisjoint : U.map f ⊓ V.map f = ⊥)
    (hinjU : Set.InjOn f (U : Set G))
    (hwitness : ∀ L : Subgroup G, B < L → ∃ n ∈ L, ∃ u ∈ U,
      n * u * n⁻¹ ∈ V ∧ n * u * n⁻¹ ≠ 1) : f.ker ≤ B :=
  (kernel_le_normalizerPullback f U).trans
    (normalizerPullback_le_upper f U V B hB hdisjoint hinjU hwitness)

theorem kernel_le_center_of_normalizing_injective_generators
    (f : G →* Q) (U V D : Subgroup G)
    (hD : f.ker ≤ D)
    (hDU : D ≤ Subgroup.normalizer (U : Set G))
    (hDV : D ≤ Subgroup.normalizer (V : Set G))
    (hinjU : Set.InjOn f (U : Set G)) (hinjV : Set.InjOn f (V : Set G))
    (hgen : U ⊔ V = ⊤) : f.ker ≤ Subgroup.center G := by
  intro k hk
  have hcentralizes (T : Subgroup G) (hnorm : D ≤ Subgroup.normalizer (T : Set G))
      (hinj : Set.InjOn f (T : Set G)) : T ≤ Subgroup.centralizer ({k} : Set G) := by
    intro t ht
    apply Subgroup.mem_centralizer_iff.mpr
    intro x hx
    have hxk : x = k := Set.mem_singleton_iff.mp hx
    subst x
    have hc : k * t * k⁻¹ ∈ T :=
      (Subgroup.mem_normalizer_iff.mp (hnorm (hD hk)) t).mp ht
    have he : f (k * t * k⁻¹) = f t := by
      rw [map_mul, map_mul, map_inv, show f k = 1 from hk, one_mul, inv_one, mul_one]
    have hraw := congrArg (fun z : G => z * k) (hinj hc ht he)
    simpa only [mul_assoc, inv_mul_cancel, mul_one] using hraw
  have hall : (⊤ : Subgroup G) ≤ Subgroup.centralizer ({k} : Set G) := by
    rw [← hgen]
    exact sup_le (hcentralizes U hDU hinjU) (hcentralizes V hDV hinjV)
  apply Subgroup.mem_center_iff.mpr
  intro g
  exact (Subgroup.mem_centralizer_iff.mp (hall (Subgroup.mem_top g)) k
    (Set.mem_singleton k)).symm

theorem kernel_le_center_of_injective_conjugate_generators
    (f : G →* Q) (U : Subgroup G) (w : G)
    (hker : f.ker ≤ Subgroup.normalizer (U : Set G))
    (hinjU : Set.InjOn f (U : Set G))
    (hgen : U ⊔ U.map (MulAut.conj w).toMonoidHom = ⊤) :
    f.ker ≤ Subgroup.center G := by
  have hU : U ≤ Subgroup.centralizer (f.ker : Set G) := by
    intro u hu
    apply Subgroup.mem_centralizer_iff.mpr
    intro k hk
    have hc : k * u * k⁻¹ ∈ U :=
      (Subgroup.mem_normalizer_iff.mp (hker hk) u).mp hu
    have he : f (k * u * k⁻¹) = f u := by
      rw [map_mul, map_mul, map_inv, show f k = 1 from hk, one_mul, inv_one, mul_one]
    have hh := congrArg (fun z : G => z * k) (hinjU hc hu he)
    simpa only [mul_assoc, inv_mul_cancel, mul_one] using hh
  have hV : U.map (MulAut.conj w).toMonoidHom ≤
      Subgroup.centralizer (f.ker : Set G) := by
    rintro _ ⟨u, hu, rfl⟩
    exact (inferInstance : (Subgroup.centralizer (f.ker : Set G)).Normal).conj_mem
      u (hU hu) w
  have hall : (⊤ : Subgroup G) ≤ Subgroup.centralizer (f.ker : Set G) := by
    rw [← hgen]
    exact sup_le hU hV
  intro k hk
  apply Subgroup.mem_center_iff.mpr
  intro g
  exact (Subgroup.mem_centralizer_iff.mp (hall (Subgroup.mem_top g)) k hk).symm

end SymmetricSubgroupAsymptotics.CFSGOpposedSubgroupKernel
