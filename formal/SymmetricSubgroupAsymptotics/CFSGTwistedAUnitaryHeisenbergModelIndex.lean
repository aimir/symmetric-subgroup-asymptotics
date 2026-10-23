import SymmetricSubgroupAsymptotics.CFSGTwistedAUnitaryCentralProjectiveFaithful
import SymmetricSubgroupAsymptotics.CFSGTwistedAUnitaryHeisenbergDegree
import SymmetricSubgroupAsymptotics.CFSGTwistedAUnitaryNormalizerPSubgroups

/-! The Heisenberg lower bound on EVERY proper subgroup of the SAME
original twisted-A central quotient, rank at least three. Only the
genuine model simplicity instance is used; actual central conjugacy and
survival in the centre quotient are proved, not supplied as callbacks. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Classical

namespace SymmetricSubgroupAsymptotics.CFSGConjugateImageAction
open MulAction

theorem fixedBy_card_eq_of_conjugate {G X : Type*} [Group G] [MulAction G X]
    (a b g : G) (h : g * a * g⁻¹ = b) :
    Nat.card (fixedBy X b) = Nat.card (fixedBy X a) := by
  have he := Nat.card_congr (CFSGConjugateSubgroupDegree.fixedByConjugateEquiv (X := X) a g)
  rw [h] at he
  exact he.symm

theorem conjugate_images_of_equiv {A C G : Type*} [Group A] [Group C] [Group G]
    (e : A ≃* C) (f : C →* G) (h : A →* G) (he : ∀ a, f (e a) = h a)
    (hconj : ∀ a b : A, a ≠ 1 → b ≠ 1 → ∃ g : G, g * h a * g⁻¹ = h b)
    (x y : C) (hx : x ≠ 1) (hy : y ≠ 1) : ∃ g : G, g * f x * g⁻¹ = f y := by
  obtain ⟨a, rfl⟩ := e.surjective x
  obtain ⟨b, rfl⟩ := e.surjective y
  have ha : a ≠ 1 := fun hh => hx ((congrArg e hh).trans (MulEquiv.map_one e))
  have hb : b ≠ 1 := fun hh => hy ((congrArg e hh).trans (MulEquiv.map_one e))
  obtain ⟨g, hg⟩ := hconj a b ha hb
  refine ⟨g, ?_⟩
  simpa only [he] using hg

end SymmetricSubgroupAsymptotics.CFSGConjugateImageAction

namespace SymmetricSubgroupAsymptotics.CFSGTwistedAUnitaryCoordinates
open CFSGTwistedAUpperUnipotent CFSGTwistedAUnitaryNaturalRadical
open MulAction

def projectiveRadicalCentreHom (q : CFSG.PrimePower) (s : ℕ) :
    radicalCentre q (s + 1) →* CFSG.Models.TwistedA (s + 3) q :=
  (projectiveRadicalHom q s).comp (radicalCentre q (s + 1)).subtype

theorem projectiveRadicalCentreHom_equiv_apply (q : CFSG.PrimePower) (s : ℕ)
    (a : Multiplicative (centralParameters q (s + 1))) :
    projectiveRadicalCentreHom q s (centralRadicalKernelEquiv q (s + 1) a) =
      projectiveCentralParameterHom q s a := rfl

theorem projectiveRadicalCentreHom_injective (q : CFSG.PrimePower) (s : ℕ) :
    Function.Injective (projectiveRadicalCentreHom q s) := by
  intro x y hxy
  obtain ⟨a, rfl⟩ := (centralRadicalKernelEquiv q (s + 1)).surjective x
  obtain ⟨b, rfl⟩ := (centralRadicalKernelEquiv q (s + 1)).surjective y
  apply congrArg (centralRadicalKernelEquiv q (s + 1))
  apply projectiveCentralParameterHom_injective q s
  exact hxy

theorem projectiveRadicalCentre_conjugate (q : CFSG.PrimePower) (s : ℕ)
    (x y : radicalCentre q (s + 1)) (hx : x ≠ 1) (hy : y ≠ 1) :
    ∃ g : CFSG.Models.TwistedA (s + 3) q,
      g * projectiveRadicalCentreHom q s x * g⁻¹ = projectiveRadicalCentreHom q s y := by
  let e : Multiplicative (centralParameters q (s + 1)) ≃* radicalCentre q (s + 1) :=
    centralRadicalKernelEquiv q (s + 1)
  exact CFSGConjugateImageAction.conjugate_images_of_equiv e
    (projectiveRadicalCentreHom q s) (projectiveCentralParameterHom q s)
    (projectiveRadicalCentreHom_equiv_apply q s)
    (projectiveCentralParameter_conjugate q s) x y hx hy

theorem twistedA_shifted_finite (q : CFSG.PrimePower) (s : ℕ) :
    Finite (CFSG.Models.TwistedA (s + 3) q) := by
  letI : Finite (Fixed (s + 3) q) := originalFixed_finite q (s + 3) (by omega)
  change Finite (commutator (Fixed (s + 3) q) ⧸ Subgroup.center (commutator (Fixed (s + 3) q)))
  infer_instance

theorem exists_radicalCentre_projective_ne_one (q : CFSG.PrimePower) (s : ℕ) :
    ∃ c : radicalCentre q (s + 1), c ≠ 1 ∧ projectiveRadicalCentreHom q s c ≠ 1 := by
  obtain ⟨t, ht0, ht⟩ := exists_nonzero_central_parameter q (s + 1)
  let a : Multiplicative (centralParameters q (s + 1)) :=
    Multiplicative.ofAdd ⟨t, (centralCondition_iff q (s + 1) t).mp ht⟩
  let e : Multiplicative (centralParameters q (s + 1)) ≃* radicalCentre q (s + 1) :=
    centralRadicalKernelEquiv q (s + 1)
  have ha : a ≠ 1 := by
    intro he
    exact ht0 (congrArg (fun z : Multiplicative (centralParameters q (s + 1)) => z.toAdd.val) he)
  have hc : e a ≠ 1 := by
    intro he
    apply ha
    exact e.injective (he.trans (MulEquiv.map_one e).symm)
  refine ⟨e a, hc, ?_⟩
  intro he
  apply hc
  exact projectiveRadicalCentreHom_injective q s
    (he.trans ((projectiveRadicalCentreHom q s).map_one).symm)

theorem twistedA_shifted_field_power_le_proper_index (q : CFSG.PrimePower) (s : ℕ)
    [IsSimpleGroup (CFSG.Models.TwistedA (s + 3) q)]
    (H : Subgroup (CFSG.Models.TwistedA (s + 3) q)) (hH : H ≠ ⊤) :
    q.order ^ (s + 3) ≤ H.index := by
  let G := CFSG.Models.TwistedA (s + 3) q
  let X := G ⧸ H
  letI : Finite G := twistedA_shifted_finite q s
  letI : MulAction (fixedRadical q (s + 1)) X := MulAction.compHom X (projectiveRadicalHom q s)
  letI : MulAction (radicalCentre q (s + 1)) X := MulAction.compHom X (projectiveRadicalCentreHom q s)
  obtain ⟨c, hc, hcG⟩ := exists_radicalCentre_projective_ne_one q s
  let f := Nat.card (fixedBy X c)
  have hfix : ∀ d : radicalCentre q (s + 1), d ≠ 1 → Nat.card (fixedBy X d) = f := by
    intro d hd
    obtain ⟨g, hg⟩ := projectiveRadicalCentre_conjugate q s c d hc hd
    change Nat.card (fixedBy X (projectiveRadicalCentreHom q s d)) =
      Nat.card (fixedBy X (projectiveRadicalCentreHom q s c))
    exact CFSGConjugateImageAction.fixedBy_card_eq_of_conjugate
      (projectiveRadicalCentreHom q s c) (projectiveRadicalCentreHom q s d) g hg
  obtain ⟨x, hx⟩ := CFSGConjugateSubgroupDegree.exists_moved_coset_of_ne_one
    H hH (projectiveRadicalCentreHom q s c) hcG
  exact radical_degree_lower_of_constant_central_fixedBy (X := X)
    q (s + 1) f hfix ⟨c, x, hx⟩

end SymmetricSubgroupAsymptotics.CFSGTwistedAUnitaryCoordinates
