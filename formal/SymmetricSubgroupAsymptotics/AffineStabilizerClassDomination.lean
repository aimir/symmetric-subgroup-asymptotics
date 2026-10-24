import SymmetricSubgroupAsymptotics.AffineInertiaOrbitDomination
import Mathlib.Data.Finite.Sum

/-! For a linear action whose nonzero vectors form one actual orbit,
the inertia quotient is covered by the classes of the whole group and
one nonzero-vector stabilizer. SAME-linear-part affine inertia
domination therefore bounds every actual affine point stabilizer.
The point-orbit cover is proved, rather than supplied as a class bound. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Classical

namespace SymmetricSubgroupAsymptotics.AffineStabilizerClassDomination
open GroupActionInertia

variable {G V : Type*} [Group G] [AddCommGroup V] [DistribMulAction G V]

def zeroStabilizerHom : G →* MulAction.stabilizer G (0 : V) where
  toFun g := ⟨g, smul_zero g⟩
  map_one' := Subtype.ext rfl
  map_mul' _ _ := Subtype.ext rfl

def twoOrbitClassMap (v : V) :
    ConjClasses G ⊕ ConjClasses (MulAction.stabilizer G v) →
      MulAction.orbitRel.Quotient G (inertia G V) :=
  Sum.elim (fun c => stabilizerClassMap (G := G) (0 : V)
    (ConjClasses.map (zeroStabilizerHom (G := G) (V := V)) c))
    (stabilizerClassMap (G := G) v)

theorem twoOrbitClassMap_inl_mk (v : V) (g : G) :
    twoOrbitClassMap v (Sum.inl (ConjClasses.mk g)) =
      Quotient.mk'' (stabilizerPoint (0 : V) (zeroStabilizerHom g)) := rfl

theorem twoOrbitClassMap_inr_mk (v : V) (g : MulAction.stabilizer G v) :
    twoOrbitClassMap v (Sum.inr (ConjClasses.mk g)) =
      Quotient.mk'' (stabilizerPoint v g) := rfl

theorem twoOrbitClassMap_surjective (v : V)
    (htrans : ∀ w : V, w ≠ 0 → ∃ g : G, g • v = w) :
    Function.Surjective (twoOrbitClassMap (G := G) v) := by
  intro c
  refine Quotient.inductionOn c ?_
  intro p
  change ∃ d, twoOrbitClassMap v d = Quotient.mk'' p
  by_cases hp : p.val.2 = 0
  · refine ⟨Sum.inl (ConjClasses.mk p.val.1), ?_⟩
    rw [twoOrbitClassMap_inl_mk]
    apply congrArg (fun z : inertia G V => Quotient.mk'' z)
    apply Subtype.ext
    apply Prod.ext
    · rfl
    · exact hp.symm
  · obtain ⟨g, hg⟩ := htrans p.val.2 hp
    let a : G := g⁻¹ * p.val.1 * g
    have ha : a ∈ MulAction.stabilizer G v := by
      change (g⁻¹ * p.val.1 * g) • v = v
      rw [mul_smul, mul_smul, hg, p.property, ← hg, inv_smul_smul]
    have he : g • stabilizerPoint v (⟨a, ha⟩ : MulAction.stabilizer G v) = p := by
      apply Subtype.ext
      apply Prod.ext
      · change g * a * g⁻¹ = p.val.1
        dsimp only [a]
        group
      · exact hg
    refine ⟨Sum.inr (ConjClasses.mk (⟨a, ha⟩ : MulAction.stabilizer G v)), ?_⟩
    rw [twoOrbitClassMap_inr_mk]
    exact (Quotient.sound (show MulAction.orbitRel G (inertia G V) p
      (stabilizerPoint v (⟨a, ha⟩ : MulAction.stabilizer G v)) from ⟨g, he⟩)).symm

theorem linear_inertia_card_le [Finite G] (v : V)
    (htrans : ∀ w : V, w ≠ 0 → ∃ g : G, g • v = w) :
    Nat.card (MulAction.orbitRel.Quotient G (inertia G V)) ≤
      Nat.card (ConjClasses G) + Nat.card (ConjClasses (MulAction.stabilizer G v)) := by
  letI : Finite (ConjClasses G) :=
    Finite.of_surjective ConjClasses.mk ConjClasses.mk_surjective
  letI : Finite (ConjClasses (MulAction.stabilizer G v)) :=
    Finite.of_surjective ConjClasses.mk ConjClasses.mk_surjective
  have h := Nat.card_le_card_of_surjective (twoOrbitClassMap (G := G) v)
    (twoOrbitClassMap_surjective v htrans)
  simpa only [Nat.card_sum] using h

theorem stabilizer_class_card_le {X : Type*} [MulAction G X]
    [Finite G] [Finite X] [Finite V]
    (e : X ≃ V) (t : G → V)
    (hlinear : ∀ (g : G) (x : X), e (g • x) = t g + g • e x)
    (v : V) (htrans : ∀ w : V, w ≠ 0 → ∃ g : G, g • v = w) (x : X) :
    Nat.card (ConjClasses (MulAction.stabilizer G x)) ≤
      Nat.card (ConjClasses G) + Nat.card (ConjClasses (MulAction.stabilizer G v)) :=
  (stabilizer_class_card_le_inertia (G := G) x).trans
    ((AffineInertiaOrbitDomination.inertia_orbit_card_le e t hlinear).trans
      (linear_inertia_card_le v htrans))

end SymmetricSubgroupAsymptotics.AffineStabilizerClassDomination
