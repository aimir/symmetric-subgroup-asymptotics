import Mathlib.Algebra.Lie.Ideal
import Mathlib.LinearAlgebra.Span.Basic

/-! A central deviation vanishes on the derived Lie algebra. The realization
may have a central kernel: faithful realization of the whole Lie algebra is
not required. The actual source perfectness and kernel centrality remain
separate obligations when applying this lemma to an integral Serre model. -/
set_option autoImplicit false
namespace SymmetricSubgroupAsymptotics.PerfectLieCentralDeviation

variable {R L M : Type*} [CommRing R] [LieRing L] [LieAlgebra R L]
    [LieRing M] [LieAlgebra R M]

/-- Pointwise central deviation forces every bracket to be fixed. -/
theorem map_lie_eq_self (f : L →ₗ⁅R⁆ L)
    (hcentral : ∀ x y : L, ⁅f x - x, y⁆ = 0) (x y : L) :
    f ⁅x, y⁆ = ⁅x, y⁆ := by
  have hleft : ⁅f x, y⁆ = ⁅x, y⁆ := by
    have h := hcentral x y
    rw [sub_lie] at h
    exact sub_eq_zero.mp h
  have hright : ⁅f x, f y⁆ = ⁅f x, y⁆ := by
    have hzero : ⁅f x, f y - y⁆ = 0 := by
      simpa only [hcentral y (f x), neg_zero] using
        (lie_skew (f x) (f y - y)).symm
    rw [lie_sub] at hzero
    exact sub_eq_zero.mp hzero
  rw [LieHom.map_lie, hright, hleft]

/-- The spanning form of perfectness makes the central deviation zero. -/
theorem apply_eq_self (f : L →ₗ⁅R⁆ L)
    (hperfect : Submodule.span R
      (Set.range (fun xy : L × L => ⁅xy.1, xy.2⁆)) = ⊤)
    (hcentral : ∀ x y : L, ⁅f x - x, y⁆ = 0) (x : L) : f x = x := by
  let S : Submodule R L := LinearMap.ker (f.toLinearMap - LinearMap.id)
  have hspan : Submodule.span R
      (Set.range (fun xy : L × L => ⁅xy.1, xy.2⁆)) ≤ S := by
    apply Submodule.span_le.mpr
    rintro _ ⟨⟨u, v⟩, rfl⟩
    change f ⁅u, v⁆ - ⁅u, v⁆ = 0
    exact sub_eq_zero.mpr (map_lie_eq_self f hcentral u v)
  rw [hperfect] at hspan
  have hx : x ∈ S := hspan (show x ∈ (⊤ : Submodule R L) from trivial)
  change f x - x = 0 at hx
  exact sub_eq_zero.mp hx

theorem eq_id (f : L →ₗ⁅R⁆ L)
    (hperfect : Submodule.span R
      (Set.range (fun xy : L × L => ⁅xy.1, xy.2⁆)) = ⊤)
    (hcentral : ∀ x y : L, ⁅f x - x, y⁆ = 0) : f = LieHom.id := by
  ext x
  exact apply_eq_self f hperfect hcentral x

/-- A genuine realization with central kernel detects all endomorphisms
of a perfect source which act identically on that realization. -/
theorem eq_id_of_central_kernel (β : L →ₗ⁅R⁆ M) (f : L →ₗ⁅R⁆ L)
    (hperfect : Submodule.span R
      (Set.range (fun xy : L × L => ⁅xy.1, xy.2⁆)) = ⊤)
    (hker : ∀ z : L, β z = 0 → ∀ y : L, ⁅z, y⁆ = 0)
    (himage : ∀ x : L, β (f x) = β x) : f = LieHom.id := by
  apply eq_id f hperfect
  intro x y
  apply hker (f x - x) ?_ y
  rw [map_sub, himage, sub_self]

end SymmetricSubgroupAsymptotics.PerfectLieCentralDeviation
