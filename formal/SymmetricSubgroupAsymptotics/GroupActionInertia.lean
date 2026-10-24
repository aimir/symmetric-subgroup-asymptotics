import Mathlib.GroupTheory.GroupAction.Quotient
import Mathlib.SetTheory.Cardinal.Finite
import Mathlib.Tactic.Group

/-! The actual inertia action consists of pairs (a,x) with a fixing x.
Conjugation moves a while the original action moves x. Conjugacy
classes of every actual point stabilizer inject into the orbit quotient
of this action, with no transitivity or normality assumption. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section

namespace SymmetricSubgroupAsymptotics.GroupActionInertia

def inertia (G X : Type*) [Group G] [MulAction G X] : Set (G × X) :=
  {p | p.1 • p.2 = p.2}

variable {G X : Type*} [Group G] [MulAction G X]

instance inertiaAction : MulAction G (inertia G X) where
  smul g p := ⟨(g * p.val.1 * g⁻¹, g • p.val.2), by
    change (g * p.val.1 * g⁻¹) • (g • p.val.2) = g • p.val.2
    rw [mul_smul, mul_smul, inv_smul_smul, p.property]⟩
  one_smul p := by
    apply Subtype.ext
    apply Prod.ext
    · change (1 : G) * p.val.1 * (1 : G)⁻¹ = p.val.1
      simp only [one_mul, inv_one, mul_one]
    · exact one_smul G p.val.2
  mul_smul g h p := by
    apply Subtype.ext
    apply Prod.ext
    · change (g * h) * p.val.1 * (g * h)⁻¹ =
        g * (h * p.val.1 * h⁻¹) * g⁻¹
      group
    · exact mul_smul g h p.val.2

def stabilizerPoint (x : X) (a : MulAction.stabilizer G x) : inertia G X :=
  ⟨((a : G), x), a.property⟩

theorem stabilizer_isConj_iff_inertia_class (x : X)
    (a b : MulAction.stabilizer G x) :
    IsConj a b ↔
      (Quotient.mk'' (stabilizerPoint x a) :
        Quotient (MulAction.orbitRel G (inertia G X))) =
      Quotient.mk'' (stabilizerPoint x b) := by
  constructor
  · intro hab
    obtain ⟨t, ht⟩ := isConj_iff.mp hab
    have he : (t : G) • stabilizerPoint x a = stabilizerPoint x b := by
      apply Subtype.ext
      apply Prod.ext
      · change (t : G) * (a : G) * (t : G)⁻¹ = (b : G)
        exact congrArg (fun z : MulAction.stabilizer G x => (z : G)) ht
      · exact t.property
    exact (Quotient.sound (show MulAction.orbitRel G (inertia G X)
      (stabilizerPoint x b) (stabilizerPoint x a) from ⟨(t : G), he⟩)).symm
  · intro hab
    obtain ⟨g, hg⟩ := Quotient.exact hab
    have hfix : g • x = x := congrArg (fun p : inertia G X => p.val.2) hg
    have hconj : g * (b : G) * g⁻¹ = (a : G) :=
      congrArg (fun p : inertia G X => p.val.1) hg
    have ht : g ∈ MulAction.stabilizer G x := hfix
    exact (isConj_iff.mpr
      ⟨(⟨g, ht⟩ : MulAction.stabilizer G x), Subtype.ext hconj⟩).symm

def stabilizerClassMap (x : X) :
    ConjClasses (MulAction.stabilizer G x) →
      Quotient (MulAction.orbitRel G (inertia G X)) :=
  Quotient.lift (fun a => Quotient.mk'' (stabilizerPoint x a))
    (fun a b hab => (stabilizer_isConj_iff_inertia_class x a b).mp hab)

theorem stabilizerClassMap_mk (x : X) (a : MulAction.stabilizer G x) :
    stabilizerClassMap x (ConjClasses.mk a) = Quotient.mk'' (stabilizerPoint x a) := rfl

theorem stabilizerClassMap_injective (x : X) :
    Function.Injective (stabilizerClassMap (G := G) x) := by
  intro c d he
  obtain ⟨a, rfl⟩ := ConjClasses.mk_surjective c
  obtain ⟨b, rfl⟩ := ConjClasses.mk_surjective d
  apply ConjClasses.mk_eq_mk_iff_isConj.mpr
  exact (stabilizer_isConj_iff_inertia_class x a b).mpr he

theorem stabilizer_class_card_le_inertia [Finite G] [Finite X] (x : X) :
    Nat.card (ConjClasses (MulAction.stabilizer G x)) ≤
      Nat.card (Quotient (MulAction.orbitRel G (inertia G X))) :=
  Nat.card_le_card_of_injective (stabilizerClassMap (G := G) x)
    (stabilizerClassMap_injective (G := G) x)

end SymmetricSubgroupAsymptotics.GroupActionInertia
