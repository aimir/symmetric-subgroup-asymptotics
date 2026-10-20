import SymmetricSubgroupAsymptotics.CoinducedLeadingRows

/-! Comparable leading rows in the same actual local core orbit admit
an actual ambient-group cancellation. This is the coefficient-orbit seam
of the minimum-weight generator argument. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics.CoinducedLeadingRows
open FiniteRowLeadingWeight

variable {k G V : Type} [Field k] [Group G] [AddCommGroup V] [Module k V] {n : ℕ}

theorem same_orbit_cancellation
    (H : Subgroup G) (rho : Representation k H V) (T : Fin n → G)
    (hfactor : ∀ x : G, ∃ h : G, h∈H ∧ ∃ a : Fin n, x=h*T a)
    (rel : Fin n → Fin n → Prop)
    (hunique : ∀ a b, T a*(T b)⁻¹∈H → a=b)
    (htri : CosetTriangular H T (· < ·) rel)
    (L : Subgroup H) (hL : L.map H.subtype≤H.normalCore)
    (x y : Representation.coindV H.subtype rho) (a b : Fin n)
    (hx : HasLeading (rows H rho T x) a) (hy : HasLeading (rows H rho T y) b)
    (hab : rel a b)
    (horbit : ∃ l : L, rho (l : H) (rows H rho T x a)=rows H rho T y b) :
    ∃ g : G, weight (rows H rho T (y-(Representation.coind H.subtype rho) g x))<
      weight (rows H rho T y) := by
  let u := CoinducedLeadingCoordinates.raisingElement T a b
  obtain ⟨hx1,hcoef1⟩ := raise_leading H rho T hfactor rel hunique htri x a b hx hab
  obtain ⟨l,hl⟩ := horbit
  have hne : rho (l : H) (rows H rho T ((Representation.coind H.subtype rho) u x) b)≠0 := by
    rw [hcoef1,hl]
    exact hy.1
  obtain ⟨v,hx2,hcoef2⟩ := twist_leading H rho T L hL
    ((Representation.coind H.subtype rho) u x) b hx1 l hne
  have haction : (Representation.coind H.subtype rho) (v*u) x=
      (Representation.coind H.subtype rho) v ((Representation.coind H.subtype rho) u x) := by
    rw [map_mul]
    rfl
  have he : rows H rho T ((Representation.coind H.subtype rho) v
      ((Representation.coind H.subtype rho) u x)) b=rows H rho T y b := by
    rw [hcoef2,hcoef1,hl]
  have hdrop := cancellation_decreases_weight hx2 hy he
  refine ⟨v*u,?_⟩
  rw [haction,map_sub]
  exact hdrop

end SymmetricSubgroupAsymptotics.CoinducedLeadingRows
