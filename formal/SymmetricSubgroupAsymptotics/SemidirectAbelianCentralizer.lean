import Mathlib.GroupTheory.SemidirectProduct
import Mathlib.GroupTheory.Subgroup.Centralizer
import Mathlib.GroupTheory.QuotientGroup.Basic
import Mathlib.SetTheory.Cardinal.Finite

/-!
# Centralizers of an abelian translation group

The centralizer modulo translations is exactly the kernel of the actual
complement action. This reduces finite affine centralizer certificates to
the much smaller complement, without enumerating the affine group.
-/

set_option autoImplicit false
noncomputable section

namespace SymmetricSubgroupAsymptotics
namespace SemidirectAbelianCentralizer

open SemidirectProduct

variable {V H : Type*} [CommGroup V] [Group H]
variable (φ : H →* MulAut V)

theorem mem_centralizer_iff (g : V ⋊[φ] H) :
    g ∈ Subgroup.centralizer ((inl : V →* V ⋊[φ] H).range : Set (V ⋊[φ] H)) ↔
      φ g.right = 1 := by
  constructor
  · intro hg
    apply MulEquiv.ext
    intro v
    have h := congrArg SemidirectProduct.left
      ((Subgroup.mem_centralizer_iff.mp hg) (inl v) ⟨v, rfl⟩)
    simp only [mul_left, left_inl, right_inl, map_one, MulAut.one_apply] at h
    have : g.left * v = g.left * φ g.right v := by
      simpa only [mul_comm v g.left] using h
    exact (mul_left_cancel this).symm
  · intro hg
    rw [Subgroup.mem_centralizer_iff]
    rintro x ⟨v, rfl⟩
    apply SemidirectProduct.ext <;> simp [hg, mul_comm]

theorem centralizer_map_projection :
    (Subgroup.centralizer
      ((inl : V →* V ⋊[φ] H).range : Set (V ⋊[φ] H))).map rightHom = φ.ker := by
  ext h
  constructor
  · rintro ⟨g, hg, rfl⟩
    exact (mem_centralizer_iff φ g).mp hg
  · intro hh
    refine ⟨inr h, ?_, rightHom_inr h⟩
    exact (mem_centralizer_iff φ _).mpr hh

/-- The quotient of the affine group by translations is the complement. -/
noncomputable def quotientTranslationsEquiv :
    (V ⋊[φ] H) ⧸ (rightHom : V ⋊[φ] H →* H).ker ≃* H :=
  QuotientGroup.quotientKerEquivOfSurjective rightHom rightHom_surjective

/-- The actual centralizer image in the translation quotient has exactly
the cardinality of the complement's action kernel. -/
theorem centralizer_quotient_card :
    Nat.card ((Subgroup.centralizer
      ((inl : V →* V ⋊[φ] H).range : Set (V ⋊[φ] H))).map
        (QuotientGroup.mk' (rightHom : V ⋊[φ] H →* H).ker)) = Nat.card φ.ker := by
  let C := Subgroup.centralizer
    ((inl : V →* V ⋊[φ] H).range : Set (V ⋊[φ] H))
  let q := QuotientGroup.mk' (rightHom : V ⋊[φ] H →* H).ker
  let e := quotientTranslationsEquiv φ
  have hcomp : e.toMonoidHom.comp q = rightHom := by ext g; rfl
  have hmap : (C.map q).map e.toMonoidHom = φ.ker := by
    rw [Subgroup.map_map, hcomp]
    exact centralizer_map_projection φ
  calc
    Nat.card (C.map q) = Nat.card ((C.map q).map e.toMonoidHom) :=
      Nat.card_congr (e.subgroupMap (C.map q)).toEquiv
    _ = Nat.card φ.ker := by rw [hmap]

end SemidirectAbelianCentralizer
end SymmetricSubgroupAsymptotics

end
