import SymmetricSubgroupAsymptotics.CFSGTwistedA2HeisenbergProjectiveFaithful
import SymmetricSubgroupAsymptotics.CFSGTwistedAUnitaryHeisenbergModelIndex
import SymmetricSubgroupAsymptotics.PrimitiveSocleRawSimpleIndex

/-! The actual rank-two original model has proper-subgroup index at
least q squared. Its only structural hypothesis is the genuine model
simplicity instance; the q >= 3 guard is the classifier-admissible one.
All central conjugacy and quotient-survival inputs are proved. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Classical

namespace SymmetricSubgroupAsymptotics.CFSGTwistedAUnitaryCoordinates
open CFSGTwistedAUpperUnipotent CFSGTwistedAUnitaryNaturalRadical
open MulAction PrimitiveSocleRawStructure

def rankTwoRadicalCentreHom (q : CFSG.PrimePower) (hq : 3 ≤ q.order) :
    radicalCentre q 0 →* CFSG.Models.TwistedA 2 q :=
  (rankTwoRadicalHom q hq).comp (radicalCentre q 0).subtype

theorem rankTwoRadicalCentreHom_equiv_apply (q : CFSG.PrimePower) (hq : 3 ≤ q.order)
    (a : Multiplicative (centralParameters q 0)) :
    rankTwoRadicalCentreHom q hq (centralRadicalKernelEquiv q 0 a) =
      rankTwoCentralParameterHom q hq a := rfl

theorem rankTwoRadicalCentreHom_injective (q : CFSG.PrimePower) (hq : 3 ≤ q.order) :
    Function.Injective (rankTwoRadicalCentreHom q hq) := by
  intro x y hxy
  obtain ⟨a, rfl⟩ := (centralRadicalKernelEquiv q 0).surjective x
  obtain ⟨b, rfl⟩ := (centralRadicalKernelEquiv q 0).surjective y
  apply congrArg (centralRadicalKernelEquiv q 0)
  exact rankTwoCentralParameterHom_injective q hq hxy

theorem rankTwoRadicalCentre_conjugate (q : CFSG.PrimePower) (hq : 3 ≤ q.order)
    (x y : radicalCentre q 0) (hx : x ≠ 1) (hy : y ≠ 1) :
    ∃ g : CFSG.Models.TwistedA 2 q,
      g * rankTwoRadicalCentreHom q hq x * g⁻¹ = rankTwoRadicalCentreHom q hq y := by
  exact CFSGConjugateImageAction.conjugate_images_of_equiv
    (centralRadicalKernelEquiv q 0) (rankTwoRadicalCentreHom q hq)
    (rankTwoCentralParameterHom q hq) (rankTwoRadicalCentreHom_equiv_apply q hq)
    (rankTwoCentralParameter_conjugate q hq) x y hx hy

theorem rankTwoModel_finite (q : CFSG.PrimePower) : Finite (CFSG.Models.TwistedA 2 q) := by
  letI : Finite (Fixed 2 q) := originalFixed_finite q 2 (by decide)
  change Finite (commutator (Fixed 2 q) ⧸ Subgroup.center (commutator (Fixed 2 q)))
  infer_instance

theorem exists_rankTwoRadicalCentre_projective_ne_one (q : CFSG.PrimePower)
    (hq : 3 ≤ q.order) :
    ∃ c : radicalCentre q 0, c ≠ 1 ∧ rankTwoRadicalCentreHom q hq c ≠ 1 := by
  obtain ⟨t, ht0, ht⟩ := exists_nonzero_central_parameter q 0
  let a : Multiplicative (centralParameters q 0) :=
    Multiplicative.ofAdd ⟨t, (centralCondition_iff q 0 t).mp ht⟩
  let e : Multiplicative (centralParameters q 0) ≃* radicalCentre q 0 := centralRadicalKernelEquiv q 0
  have ha : a ≠ 1 := by
    intro he
    exact ht0 (congrArg (fun z : Multiplicative (centralParameters q 0) => z.toAdd.val) he)
  have hc : e a ≠ 1 := by
    intro he
    exact ha (e.injective (he.trans (MulEquiv.map_one e).symm))
  refine ⟨e a, hc, ?_⟩
  intro he
  exact hc (rankTwoRadicalCentreHom_injective q hq
    (he.trans ((rankTwoRadicalCentreHom q hq).map_one).symm))

theorem twistedA_rankTwo_field_square_le_proper_index (q : CFSG.PrimePower)
    (hq : 3 ≤ q.order) [IsSimpleGroup (CFSG.Models.TwistedA 2 q)]
    (H : Subgroup (CFSG.Models.TwistedA 2 q)) (hH : H ≠ ⊤) : q.order ^ 2 ≤ H.index := by
  let G := CFSG.Models.TwistedA 2 q
  let X := G ⧸ H
  letI : Finite G := rankTwoModel_finite q
  letI : MulAction (fixedRadical q 0) X := MulAction.compHom X (rankTwoRadicalHom q hq)
  letI : MulAction (radicalCentre q 0) X := MulAction.compHom X (rankTwoRadicalCentreHom q hq)
  obtain ⟨c, hc, hcG⟩ := exists_rankTwoRadicalCentre_projective_ne_one q hq
  let f := Nat.card (fixedBy X c)
  have hfix : ∀ d : radicalCentre q 0, d ≠ 1 → Nat.card (fixedBy X d) = f := by
    intro d hd
    obtain ⟨g, hg⟩ := rankTwoRadicalCentre_conjugate q hq c d hc hd
    change Nat.card (fixedBy X (rankTwoRadicalCentreHom q hq d)) =
      Nat.card (fixedBy X (rankTwoRadicalCentreHom q hq c))
    exact CFSGConjugateImageAction.fixedBy_card_eq_of_conjugate
      (rankTwoRadicalCentreHom q hq c) (rankTwoRadicalCentreHom q hq d) g hg
  obtain ⟨x, hx⟩ := CFSGConjugateSubgroupDegree.exists_moved_coset_of_ne_one
    H hH (rankTwoRadicalCentreHom q hq c) hcG
  exact radical_degree_lower_of_constant_central_fixedBy (X := X) q 0 f hfix ⟨c, x, hx⟩

theorem twistedA_rankTwo_field_square_le_leastProperIndex (q : CFSG.PrimePower)
    (hq : 3 ≤ q.order) [IsSimpleGroup (CFSG.Models.TwistedA 2 q)] (ell : ℕ)
    (hell : LeastProperIndex (CFSG.Models.TwistedA 2 q) ell) : q.order ^ 2 ≤ ell := by
  obtain ⟨H, hH, he⟩ := hell.1
  rw [← he]
  exact twistedA_rankTwo_field_square_le_proper_index q hq H hH

end SymmetricSubgroupAsymptotics.CFSGTwistedAUnitaryCoordinates
