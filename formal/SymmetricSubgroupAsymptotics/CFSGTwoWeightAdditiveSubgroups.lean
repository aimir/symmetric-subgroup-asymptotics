import Mathlib.Algebra.Group.Subgroup.Basic
import Mathlib.Algebra.Field.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

/-! Independent scalar actions on two additive field coordinates
force every invariant subgroup to be a sum of coordinate axes. This
is proved by subtraction, not by module or representation classification. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGTwoWeightAdditiveSubgroups
variable {K : Type*} [Field K]

def leftAxis : AddSubgroup (K × K) := (⊤ : AddSubgroup K).prod ⊥
def rightAxis : AddSubgroup (K × K) := (⊥ : AddSubgroup K).prod ⊤

theorem coordinate_members (H : AddSubgroup (K × K))
    (hleft : ∀ u : Kˣ, ∀ x ∈ H, ((u : K) * x.1, x.2) ∈ H)
    (u : Kˣ) (hu : (u : K) ≠ 1) (x : K × K) (hx : x ∈ H) :
    (x.1, 0) ∈ H ∧ (0, x.2) ∈ H := by
  have hdiff : (((u : K) - 1) * x.1, 0) ∈ H := by
    have hh := H.sub_mem (hleft u x hx) hx
    convert hh using 1 <;> ext <;> simp only [Prod.fst_sub, Prod.snd_sub] <;> ring
  have hunit : (u : K) - 1 ≠ 0 := sub_ne_zero.mpr hu
  let v : Kˣ := Units.mk0 (((u : K) - 1)⁻¹) (inv_ne_zero hunit)
  have hl : (x.1, 0) ∈ H := by
    have hh := hleft v _ hdiff
    simpa only [v, Units.val_mk0, ← mul_assoc, inv_mul_cancel₀ hunit, one_mul] using hh
  refine ⟨hl, ?_⟩
  have hh := H.sub_mem hx hl
  have he : x - (x.1, 0) = (0, x.2) := Prod.ext (sub_self x.1) (sub_zero x.2)
  exact he ▸ hh

theorem classification (H : AddSubgroup (K × K))
    (hleft : ∀ u : Kˣ, ∀ x ∈ H, ((u : K) * x.1, x.2) ∈ H)
    (hright : ∀ u : Kˣ, ∀ x ∈ H, (x.1, (u : K) * x.2) ∈ H)
    (u : Kˣ) (hu : (u : K) ≠ 1) :
    H = ⊥ ∨ H = leftAxis ∨ H = rightAxis ∨ H = ⊤ := by
  have hcoords := coordinate_members H hleft u hu
  have hfullleft : (∃ x ∈ H, x.1 ≠ 0) → ∀ a : K, (a, 0) ∈ H := by
    rintro ⟨x, hx, hxa⟩ a
    by_cases ha : a = 0
    · subst a
      exact H.zero_mem
    let v : Kˣ := Units.mk0 (a / x.1) (div_ne_zero ha hxa)
    have hh := hleft v _ (hcoords x hx).1
    simpa only [v, Units.val_mk0, div_mul_cancel₀ _ hxa] using hh
  have hfullright : (∃ x ∈ H, x.2 ≠ 0) → ∀ b : K, (0, b) ∈ H := by
    rintro ⟨x, hx, hxb⟩ b
    by_cases hb : b = 0
    · subst b
      exact H.zero_mem
    let v : Kˣ := Units.mk0 (b / x.2) (div_ne_zero hb hxb)
    have hh := hright v _ (hcoords x hx).2
    simpa only [v, Units.val_mk0, div_mul_cancel₀ _ hxb] using hh
  by_cases hl : ∃ x ∈ H, x.1 ≠ 0
  · by_cases hr : ∃ x ∈ H, x.2 ≠ 0
    · right; right; right
      apply top_unique
      intro x _
      have hh := H.add_mem (hfullleft hl x.1) (hfullright hr x.2)
      simpa only [Prod.mk_add_mk, add_zero, zero_add] using hh
    · right; left
      apply le_antisymm
      · intro x hx
        have hz : x.2 = 0 := not_ne_iff.mp (fun hn => hr ⟨x, hx, hn⟩)
        exact ⟨AddSubgroup.mem_top _, hz⟩
      · intro x hx
        have hz : x.2 = 0 := hx.2
        have hh := hfullleft hl x.1
        have he : x = (x.1, 0) := Prod.ext rfl hz
        exact he.symm ▸ hh
  · by_cases hr : ∃ x ∈ H, x.2 ≠ 0
    · right; right; left
      apply le_antisymm
      · intro x hx
        have hz : x.1 = 0 := not_ne_iff.mp (fun hn => hl ⟨x, hx, hn⟩)
        exact ⟨hz, AddSubgroup.mem_top _⟩
      · intro x hx
        have hz : x.1 = 0 := hx.1
        have hh := hfullright hr x.2
        have he : x = (0, x.2) := Prod.ext hz rfl
        exact he.symm ▸ hh
    · left
      apply le_antisymm ?_ bot_le
      intro x hx
      have ha : x.1 = 0 := not_ne_iff.mp (fun hn => hl ⟨x, hx, hn⟩)
      have hb : x.2 = 0 := not_ne_iff.mp (fun hn => hr ⟨x, hx, hn⟩)
      exact Prod.ext ha hb

end SymmetricSubgroupAsymptotics.CFSGTwoWeightAdditiveSubgroups
