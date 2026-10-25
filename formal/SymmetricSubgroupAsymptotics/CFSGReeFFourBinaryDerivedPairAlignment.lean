import SymmetricSubgroupAsymptotics.NormalSylowAmbientPairAlignment
import SymmetricSubgroupAsymptotics.CFSGReeFFourBinaryOppositePosition
import SymmetricSubgroupAsymptotics.CFSGReeFFourAllParameterDerivedPositive
import SymmetricSubgroupAsymptotics.CFSGReeFFourFixedPositiveSylow

/-! Every disjoint ordered binary DERIVED Sylow pair is aligned by actual
FULL fixed-group conjugation. The pair is lifted to ambient Sylows, never
an automorphism. The aligning g is retained in G and is not asserted in D.
All standard positive/opposite groups are the literal previously checked
subgroups; there is no form/group recognition or Out estimate hypothesis. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Pointwise
namespace SymmetricSubgroupAsymptotics.CFSGReeFFourBinaryDerivedPairAlignment
open CFSGReeFFourFixedModelEquivalence CFSGReeFFourFixedAmbientHom
open CFSGReeFFourFixedPositiveFamilies CFSGReeFFourFixedPositiveSylow
open CFSGReeFFourDerivedAmbientHom CFSGReeFFourDerivedOppositeSylow
open CFSGReeFFourAllParameterDerivedPositive CFSGReeFFourOppositionFixedPositiveNegative
open CFSGReeFFourBinaryOppositePosition CFSGReeFFourFixedOppositeAlignment
open CFSGSubgroupConjugateDisjoint SubgroupActionIntersectionTransport
open NormalSylowAmbientPairAlignment
local instance : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
private instance fixedFinite (m : ℕ) : Finite (originalModelFixed m) :=
  Finite.of_injective (fixedAmbientHom m) (fixedAmbientHom_injective m)

def ambientNegativeSylow (m : ℕ) : Sylow 2 (originalModelFixed m) :=
  (fixedPositiveSylow m).mapSurjective
    (f := (MulAut.conj (oppositionFixed m)).toMonoidHom) (MulAut.conj (oppositionFixed m)).surjective

theorem ambientNegativeSylow_coe (m : ℕ) :
    (ambientNegativeSylow m : Subgroup (originalModelFixed m)) = fixedNegative m := by
  change (fixedPositiveSylow m : Subgroup (originalModelFixed m)).map
    (MulAut.conj (oppositionFixed m)).toMonoidHom = _
  rw [fixedPositiveSylow_coe]
  exact fixed_positive_image_eq_fixed_negative m

theorem negativeSylow_eq_comap (m : ℕ) :
    (negativeSylow m : Subgroup (commutator (originalModelFixed m))) =
      (fixedNegative m).comap (commutator (originalModelFixed m)).subtype := by
  have h := normal_comap_conjugate (commutator (originalModelFixed m))
    (fixedPositive m) (oppositionFixed m)
  rw [fixed_positive_image_eq_fixed_negative] at h
  exact (negativeSylow_coe m).trans h.symm

theorem full_positive_map_intersection_bot (g : originalModelFixed 0)
    (h : derivedPositive 0 ⊓ (derivedPositive 0).map (MulAut.conjNormal g).toMonoidHom = ⊥) :
    fixedPositive 0 ⊓ (fixedPositive 0).map (MulAut.conj g).toMonoidHom = ⊥ := by
  obtain ⟨b, hb, he⟩ := full_opposite_conjugate_by_positive g h
  have hn : b ∈ Subgroup.normalizer (fixedPositive 0 : Set (originalModelFixed 0)) :=
    (fixedPositive 0).le_normalizer hb
  exact (congrArg (fun T : Subgroup (originalModelFixed 0) => fixedPositive 0 ⊓ T) he).trans
    ((inf_conjugate_eq_bot_iff (fixedPositive 0) (fixedNegative 0) b hn).mpr
      (CFSGReeFFourDerivedOppositeSylow.fixed_positive_inf_negative 0))

theorem ambient_pair_alignment (R S : Sylow 2 (originalModelFixed 0))
    (h : (R : Subgroup (originalModelFixed 0)).comap
        (commutator (originalModelFixed 0)).subtype ⊓
      (S : Subgroup (originalModelFixed 0)).comap
        (commutator (originalModelFixed 0)).subtype = ⊥) :
    ∃ g : originalModelFixed 0,
      (R : Subgroup (originalModelFixed 0)).map (MulAut.conj g).toMonoidHom = fixedPositive 0 ∧
      (S : Subgroup (originalModelFixed 0)).map (MulAut.conj g).toMonoidHom = fixedNegative 0 := by
  have hc : (R : Subgroup (originalModelFixed 0)) ⊓ (S : Subgroup (originalModelFixed 0)) = ⊥ := by
    apply ambient_intersection_bot_of_normal_restrictions
      (commutator (originalModelFixed 0)) (fixedPositiveSylow 0) R S _ h
    intro a ha
    rw [fixedPositiveSylow_coe] at ha ⊢
    exact full_positive_map_intersection_bot a ha
  obtain ⟨g, hgR, hgS⟩ := exists_conj_pair (fixedPositiveSylow 0) (ambientNegativeSylow 0) R S hc
    (fun a ha => by
      have hpos : fixedPositive 0 ⊓ (fixedPositive 0).map (MulAut.conj a).toMonoidHom = ⊥ := by
        simpa only [fixedPositiveSylow_coe] using ha
      obtain ⟨b, hb, he⟩ := fixed_opposite_conjugate_by_positive 0 a hpos
      have hbs : b ∈ (fixedPositiveSylow 0 : Subgroup (originalModelFixed 0)) := by
        simpa only [fixedPositiveSylow_coe] using hb
      refine ⟨b, (fixedPositiveSylow 0 : Subgroup (originalModelFixed 0)).le_normalizer hbs, ?_⟩
      simpa only [fixedPositiveSylow_coe, ambientNegativeSylow_coe] using he)
  refine ⟨g, ?_, ?_⟩
  · exact (congrArg (fun T : Sylow 2 (originalModelFixed 0) => (T : Subgroup (originalModelFixed 0))) hgR).trans
      (fixedPositiveSylow_coe 0)
  · exact (congrArg (fun T : Sylow 2 (originalModelFixed 0) => (T : Subgroup (originalModelFixed 0))) hgS).trans
      (ambientNegativeSylow_coe 0)

theorem exists_ambient_conjugating_pair
    (P Q : Sylow 2 (commutator (originalModelFixed 0)))
    (h : (P : Subgroup (commutator (originalModelFixed 0))) ⊓
      (Q : Subgroup (commutator (originalModelFixed 0))) = ⊥) :
    ∃ g : originalModelFixed 0,
      (P : Subgroup (commutator (originalModelFixed 0))).map
        (MulAut.conjNormal g).toMonoidHom = derivedPositive 0 ∧
      (Q : Subgroup (commutator (originalModelFixed 0))).map
        (MulAut.conjNormal g).toMonoidHom =
          (fixedNegative 0).comap (commutator (originalModelFixed 0)).subtype := by
  obtain ⟨R, hR⟩ := P.exists_comap_subtype_eq
  obtain ⟨S, hS⟩ := Q.exists_comap_subtype_eq
  obtain ⟨g, hgR, hgS⟩ := ambient_pair_alignment R S (by rw [hR, hS]; exact h)
  refine ⟨g, ?_, ?_⟩
  · calc
      _ = ((R : Subgroup (originalModelFixed 0)).comap
          (commutator (originalModelFixed 0)).subtype).map (MulAut.conjNormal g).toMonoidHom :=
        congrArg (fun T : Subgroup (commutator (originalModelFixed 0)) =>
          T.map (MulAut.conjNormal g).toMonoidHom) hR.symm
      _ = ((R : Subgroup (originalModelFixed 0)).map (MulAut.conj g).toMonoidHom).comap
          (commutator (originalModelFixed 0)).subtype :=
        (normal_comap_conjugate (commutator (originalModelFixed 0)) (R : Subgroup _) g).symm
      _ = (fixedPositive 0).comap (commutator (originalModelFixed 0)).subtype :=
        congrArg (fun T : Subgroup (originalModelFixed 0) =>
          T.comap (commutator (originalModelFixed 0)).subtype) hgR
  · calc
      _ = ((S : Subgroup (originalModelFixed 0)).comap
          (commutator (originalModelFixed 0)).subtype).map (MulAut.conjNormal g).toMonoidHom :=
        congrArg (fun T : Subgroup (commutator (originalModelFixed 0)) =>
          T.map (MulAut.conjNormal g).toMonoidHom) hS.symm
      _ = ((S : Subgroup (originalModelFixed 0)).map (MulAut.conj g).toMonoidHom).comap
          (commutator (originalModelFixed 0)).subtype :=
        (normal_comap_conjugate (commutator (originalModelFixed 0)) (S : Subgroup _) g).symm
      _ = (fixedNegative 0).comap (commutator (originalModelFixed 0)).subtype :=
        congrArg (fun T : Subgroup (originalModelFixed 0) =>
          T.comap (commutator (originalModelFixed 0)).subtype) hgS

end SymmetricSubgroupAsymptotics.CFSGReeFFourBinaryDerivedPairAlignment
