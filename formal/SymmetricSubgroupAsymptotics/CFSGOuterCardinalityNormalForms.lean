import SymmetricSubgroupAsymptotics.PrimitiveSocleRawSimpleIndex
import Mathlib.GroupTheory.QuotientGroup.Basic

/-! Outer classes counted by actual inner-normalized automorphism
forms. A label need not be realized, and normalization need not be
unique: uniqueness of the normalized automorphism for each label is
enough. Every normalization is retained as a genuine inner adjustment. -/
set_option autoImplicit false
noncomputable section

namespace SymmetricSubgroupAsymptotics.CFSGOuterCardinalityNormalForms
open PrimitiveSocleRawStructure
variable {G : Type} [Group G] [Finite G]

theorem outer_card_le_of_inner_normal_forms {L : Type*} [Finite L]
    (P : MulAut G → L → Prop)
    (hcover : ∀ f : MulAut G, ∃ (z : G) (g : MulAut G) (l : L),
      (∀ x : G, g x = z * f x * z⁻¹) ∧ P g l)
    (hunique : ∀ (l : L) (f g : MulAut G), P f l → P g l → f = g) :
    Nat.card (Outer G) ≤ Nat.card L := by
  classical
  let out : MulAut G →* Outer G := QuotientGroup.mk' (Inner G)
  have hkill (z : G) : out (MulAut.conj z) = 1 :=
    (QuotientGroup.eq_one_iff _).mpr ⟨z,rfl⟩
  have hex (o : Outer G) : ∃ l : L, ∃ g : MulAut G, P g l ∧ out g = o := by
    obtain ⟨f,hf⟩ := QuotientGroup.mk'_surjective (Inner G) o
    obtain ⟨z,g,l,hinner,hP⟩ := hcover f
    refine ⟨l,g,hP,?_⟩
    have hg : g = MulAut.conj z * f := by
      apply MulEquiv.ext
      intro x
      exact hinner x
    rw [hg, map_mul, hkill, one_mul]
    exact hf
  let label (o : Outer G) : L := Classical.choose (hex o)
  let normal (o : Outer G) : MulAut G := Classical.choose (Classical.choose_spec (hex o))
  have hP (o : Outer G) : P (normal o) (label o) :=
    (Classical.choose_spec (Classical.choose_spec (hex o))).1
  have ho (o : Outer G) : out (normal o) = o :=
    (Classical.choose_spec (Classical.choose_spec (hex o))).2
  apply Nat.card_le_card_of_injective label
  intro o p he
  have hn : normal o = normal p :=
    hunique (label o) (normal o) (normal p) (hP o) (by rw [he]; exact hP p)
  exact (ho o).symm.trans ((congrArg out hn).trans (ho p))

end SymmetricSubgroupAsymptotics.CFSGOuterCardinalityNormalForms
