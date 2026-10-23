import Mathlib.Algebra.Group.Hom.Basic
import Mathlib.Algebra.Group.Commute.Basic

/-! Fixed points in a literal product of two commuting root charts.
The product chart must actually be injective. An involution swapping
its factors then has precisely the coefficient graph as its fixed
points; no fixed-point surjectivity for a quotient is assumed. -/
set_option autoImplicit false
set_option Elab.async false
namespace SymmetricSubgroupAsymptotics.CFSGFixedOrthogonalPairChart
variable {A G : Type*} [Group G]

theorem swap_product (T : G →* G) (sigma : A → A) (x y : A → G)
    (hxy : ∀ a b, Commute (x a) (y b))
    (hx : ∀ a, T (x a) = y (sigma a)) (hy : ∀ b, T (y b) = x (sigma b))
    (a b : A) : T (x a * y b) = x (sigma b) * y (sigma a) := by
  rw [map_mul, hx, hy]
  exact (hxy (sigma b) (sigma a)).eq.symm

theorem fixed_pair_iff (T : G →* G) (sigma : A → A) (x y : A → G)
    (hxy : ∀ a b, Commute (x a) (y b))
    (hprod : Function.Injective (fun p : A × A => x p.1 * y p.2))
    (hx : ∀ a, T (x a) = y (sigma a)) (hy : ∀ b, T (y b) = x (sigma b))
    (a b : A) : T (x a * y b) = x a * y b ↔ a = sigma b ∧ b = sigma a := by
  rw [swap_product T sigma x y hxy hx hy]
  constructor
  · intro h
    have he : (sigma b, sigma a) = (a, b) := hprod h
    exact ⟨(congrArg Prod.fst he).symm, (congrArg Prod.snd he).symm⟩
  · rintro ⟨ha, hb⟩
    rw [← ha, ← hb]

theorem fixed_pair_iff_graph (T : G →* G) (sigma : A → A)
    (hsigma : Function.Involutive sigma) (x y : A → G)
    (hxy : ∀ a b, Commute (x a) (y b))
    (hprod : Function.Injective (fun p : A × A => x p.1 * y p.2))
    (hx : ∀ a, T (x a) = y (sigma a)) (hy : ∀ b, T (y b) = x (sigma b))
    (a b : A) : T (x a * y b) = x a * y b ↔ b = sigma a := by
  rw [fixed_pair_iff T sigma x y hxy hprod hx hy]
  constructor
  · exact And.right
  · intro hb
    refine ⟨?_, hb⟩
    rw [hb, hsigma a]

theorem exists_graph_parameter_of_fixed (T : G →* G) (sigma : A → A)
    (hsigma : Function.Involutive sigma) (x y : A → G)
    (hxy : ∀ a b, Commute (x a) (y b))
    (hprod : Function.Injective (fun p : A × A => x p.1 * y p.2))
    (hx : ∀ a, T (x a) = y (sigma a)) (hy : ∀ b, T (y b) = x (sigma b))
    (g : G) (hg : ∃ a b, g = x a * y b) (hfixed : T g = g) :
    ∃ a, g = x a * y (sigma a) := by
  obtain ⟨a, b, rfl⟩ := hg
  have hb := (fixed_pair_iff_graph T sigma hsigma x y hxy hprod hx hy a b).mp hfixed
  exact ⟨a, congrArg (fun c => x a * y c) hb⟩

end SymmetricSubgroupAsymptotics.CFSGFixedOrthogonalPairChart
