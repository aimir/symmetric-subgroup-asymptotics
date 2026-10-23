import Mathlib.GroupTheory.GroupAction.Defs
import Mathlib.SetTheory.Cardinal.Finite

/-! Two actual axis charts and an injected pointwise pair stabilizer
give a product lower bound for a finite group. The selectors are chosen
from proved orbit witnesses; no transitivity or order formula is assumed. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGTwoAxisChartCardinality
variable {G H X A B : Type*} [Group G] [Group H] [MulAction G X]

theorem product_card_le [Finite G] [Finite A] [Finite B] [Finite H]
    (e f : X) (v : A → X) (w : B → X)
    (hv : Function.Injective v) (hw : Function.Injective w)
    (hs : ∀ a, ∃ g : G, g • e = v a)
    (ht : ∀ b, ∃ g : G, g • e = e ∧ g • f = w b)
    (ι : H →* G) (hι : Function.Injective ι)
    (hfix : ∀ h, ι h • e = e ∧ ι h • f = f) :
    Nat.card A * (Nat.card B * Nat.card H) ≤ Nat.card G := by
  classical
  let s : A → G := fun a => Classical.choose (hs a)
  let t : B → G := fun b => Classical.choose (ht b)
  have hse (a : A) : s a • e = v a := Classical.choose_spec (hs a)
  have hte (b : B) : t b • e = e := (Classical.choose_spec (ht b)).1
  have htf (b : B) : t b • f = w b := (Classical.choose_spec (ht b)).2
  let F : A × (B × H) → G := fun x => s x.1 * (t x.2.1 * ι x.2.2)
  have hinj : Function.Injective F := by
    rintro ⟨a, b, h⟩ ⟨a', b', h'⟩ he
    have hee := congrArg (fun g : G => g • e) he
    change (s a * (t b * ι h)) • e = (s a' * (t b' * ι h')) • e at hee
    simp only [mul_smul, (hfix h).1, (hfix h').1, hte, hse] at hee
    have ha : a = a' := hv hee
    subst a'
    have he' : t b * ι h = t b' * ι h' := mul_left_cancel he
    have hef := congrArg (fun g : G => g • f) he'
    simp only [mul_smul, (hfix h).2, (hfix h').2, htf] at hef
    have hb : b = b' := hw hef
    subst b'
    have hh : h = h' := hι (mul_left_cancel he')
    subst h'
    rfl
  simpa only [Nat.card_prod] using Nat.card_le_card_of_injective F hinj

end SymmetricSubgroupAsymptotics.CFSGTwoAxisChartCardinality
