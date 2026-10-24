import SymmetricSubgroupAsymptotics.BilinearFixedFreeConjugacyFusion
import SymmetricSubgroupAsymptotics.LinearNonzeroConjugacyCover

/-! A genuine general-linear class code on the fixed-free elements
bounds the fixed-free classes of the SAME polar-preserver group. The
remaining classes are charged to its actual nonzero-vector stabilizer.
The code and its separating property are explicit inputs to this generic
counting lemma; no numerical class bound is asserted without them. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section

namespace SymmetricSubgroupAsymptotics.BilinearFixedFreeClassInjection
open QuadraticIsometryPolarStabilizer LinearNonzeroConjugacyCover
open FixedFreeConjugacyClassCover
variable {K V : Type*} [Field K] [CharP K 2] [AddCommGroup V] [Module K V]
    [Finite V] [Nontrivial V]

def classCode (B : LinearMap.BilinForm K V) {C : Type*} (code : polarPreservers B → C) :
    letI := nonzeroAction (polarPreservers B).subtype
    FreeClasses (G := polarPreservers B) (X := {v : V // v ≠ 0}) → C :=
  fun c => code c.2.choose

theorem classCode_injective (B : LinearMap.BilinForm K V)
    (hB : B.Nondegenerate) (hBs : B.IsSymm) {C : Type*} (code : polarPreservers B → C)
    (hcode : ∀ g h : polarPreservers B,
      (∀ v : V, g.val v = v → v = 0) → (∀ v : V, h.val v = v → v = 0) →
      code g = code h → IsConj g.val h.val) :
    letI := nonzeroAction (polarPreservers B).subtype
    Function.Injective (classCode B code) := by
  letI := nonzeroAction (polarPreservers B).subtype
  intro c d he
  let g := c.2.choose
  let h := d.2.choose
  have hg : ConjClasses.mk g = c.1 := c.2.choose_spec.1
  have hh : ConjClasses.mk h = d.1 := d.2.choose_spec.1
  have hgf : ∀ v : V, g.val v = v → v = 0 :=
    (fixedFree_iff (polarPreservers B).subtype g).mp c.2.choose_spec.2
  have hhf : ∀ v : V, h.val v = v → v = 0 :=
    (fixedFree_iff (polarPreservers B).subtype h).mp d.2.choose_spec.2
  have hc : IsConj g h := BilinearFixedFreeConjugacyFusion.isConj_of_fixedFree
    B hB hBs g h hgf (hcode g h hgf hhf he)
  apply Subtype.ext
  exact hg.symm.trans ((ConjClasses.mk_eq_mk_iff_isConj.mpr hc).trans hh)

theorem class_card_le_stabilizer_add_code (B : LinearMap.BilinForm K V)
    (hB : B.Nondegenerate) (hBs : B.IsSymm) {C : Type*} [Finite C]
    (code : polarPreservers B → C)
    (hcode : ∀ g h : polarPreservers B,
      (∀ v : V, g.val v = v → v = 0) → (∀ v : V, h.val v = v → v = 0) →
      code g = code h → IsConj g.val h.val)
    (v : V) (hv : v ≠ 0)
    (htrans : ∀ w : V, w ≠ 0 → ∃ g : polarPreservers B, g.val v = w) :
    letI := BilinearContragredientDuality.naturalAction (polarPreservers B).subtype
    Nat.card (ConjClasses (polarPreservers B)) ≤
      Nat.card (ConjClasses (MulAction.stabilizer (polarPreservers B) v)) + Nat.card C := by
  letI : Finite (V ≃ₗ[K] V) := Finite.of_injective
    (fun T : V ≃ₗ[K] V => (T : V → V)) LinearEquiv.coe_injective
  letI := BilinearContragredientDuality.naturalAction (polarPreservers B).subtype
  letI := nonzeroAction (polarPreservers B).subtype
  have hcover := LinearNonzeroConjugacyCover.class_card_le
    (polarPreservers B).subtype v hv htrans
  exact hcover.trans (Nat.add_le_add_left
    (Nat.card_le_card_of_injective (classCode B code)
      (classCode_injective B hB hBs code hcode)) _)

end SymmetricSubgroupAsymptotics.BilinearFixedFreeClassInjection
