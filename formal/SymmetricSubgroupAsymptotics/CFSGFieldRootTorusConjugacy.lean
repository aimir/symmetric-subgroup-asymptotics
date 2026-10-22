import Mathlib.Algebra.Group.Subgroup.Ker
import Mathlib.Algebra.Group.TypeTags.Basic
import Mathlib.Algebra.Field.Basic
import Mathlib.SetTheory.Cardinal.Finite
import Mathlib.Tactic.FieldSimp

/-! Full field-unit scaling makes all nonidentity elements in a literal
additive root image conjugate. No simple-group classification is used. -/
set_option autoImplicit false
noncomputable section

namespace SymmetricSubgroupAsymptotics.CFSGFieldRootTorusConjugacy
variable {K G : Type*} [Field K] [Group G]

theorem nonidentity_range_conjugate (u : Multiplicative K →* G)
    (hscale : ∀ t : Kˣ, ∃ g : G, ∀ a : K,
      g * u (Multiplicative.ofAdd a) * g⁻¹ =
        u (Multiplicative.ofAdd (a * (t : K)))) :
    ∀ a b : u.range, a ≠ 1 → b ≠ 1 →
      ∃ g : G, g * a.val * g⁻¹ = b.val := by
  intro a b ha hb
  obtain ⟨x, hx⟩ := a.property
  obtain ⟨y, hy⟩ := b.property
  have hx0 : x.toAdd ≠ 0 := by
    intro h
    have hx1 : x = 1 := Multiplicative.toAdd.injective h
    apply ha
    apply Subtype.ext
    rw [← hx, hx1, map_one]
    rfl
  have hy0 : y.toAdd ≠ 0 := by
    intro h
    have hy1 : y = 1 := Multiplicative.toAdd.injective h
    apply hb
    apply Subtype.ext
    rw [← hy, hy1, map_one]
    rfl
  let t : Kˣ := Units.mk0 (y.toAdd / x.toAdd) (div_ne_zero hy0 hx0)
  obtain ⟨g, hg⟩ := hscale t
  refine ⟨g, ?_⟩
  rw [← hx, ← hy]
  have hparam : x.toAdd * (t : K) = y.toAdd := by
    change x.toAdd * (y.toAdd / x.toAdd) = y.toAdd
    field_simp
  simpa only [hparam] using hg x.toAdd

theorem range_card (u : Multiplicative K →* G) (hu : Function.Injective u) :
    Nat.card u.range = Nat.card K := by
  calc
    _ = Nat.card (Multiplicative K) :=
      (Nat.card_congr (MonoidHom.ofInjective hu).toEquiv).symm
    _ = Nat.card K := Nat.card_congr (Multiplicative.toAdd : Multiplicative K ≃ K)

end SymmetricSubgroupAsymptotics.CFSGFieldRootTorusConjugacy
