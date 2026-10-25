import SymmetricSubgroupAsymptotics.CFSGReeFFourBinaryRelativeIntersection
import SymmetricSubgroupAsymptotics.SubgroupActionIntersectionTransport
import SymmetricSubgroupAsymptotics.CFSGReeFFourBinaryMiddleGenerators
import SymmetricSubgroupAsymptotics.CFSGReeFFourFixedOppositeAlignment

/-! Disjoint positive intersections in the binary DERIVED group force
opposition for the full fixed-group Sylows. The actual Bruhat outside
factors act by ambient conjugation on D. The aligning positive conjugator
belongs to the FULL fixed group; it is never silently asserted to lie in D.
No quotient automorphism is lifted and no Out estimate is assumed. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGReeFFourBinaryOppositePosition
open CFSGReeFFourFixedModelEquivalence CFSGReeFFourFixedAmbientHom
open CFSGReeFFourDerivedAmbientHom CFSGReeFFourFixedPositiveFamilies
open CFSGReeFFourFixedPositiveCardinality CFSGReeFFourShortPairedWeylMenu
open CFSGReeFFourBinaryRelativeIntersection CFSGReeFFourReducedPositiveIntersection
open CFSGReeFFourBinaryMiddleGenerators CFSGReeFFourFixedBruhatCover
open CFSGReeFFourFixedOppositeAlignment CFSGReeFFourOppositionFixedPositiveNegative
open SubgroupActionIntersectionTransport
private instance fixedFinite (m : ℕ) : Finite (originalModelFixed m) :=
  Finite.of_injective (fixedAmbientHom m) (fixedAmbientHom_injective m)

private theorem cell_iff_of_eq {G H : Type*} [Group G] [Group H]
    (rho : G →* MulAut H) (P : Subgroup H) (g u w v : G) (hg : g = u*w*v)
    (hu : ∀ x : H, rho u x ∈ P ↔ x ∈ P)
    (hv : ∀ x : H, rho v x ∈ P ↔ x ∈ P) :
    P ⊓ P.comap (rho g).toMonoidHom = ⊥ ↔ P ⊓ P.comap (rho w).toMonoidHom = ⊥ := by
  rw [hg]
  exact comap_intersection_mul_eq_bot_iff rho P u w v hu hv

theorem derived_shortIntersection_eq (m : ℕ) (i : Fin 16) :
    shortDerivedIntersection m i = derivedPositive m ⊓
      (derivedPositive m).comap (MulAut.conjNormal (shortModelWord m i)).toMonoidHom := by
  ext x
  rfl

theorem derived_intersection_cell_eq_bot_iff (m : ℕ) (u w v : originalModelFixed m)
    (hu : u ∈ fixedPositive m) (hv : v ∈ fixedPositive m) :
    derivedPositive m ⊓ (derivedPositive m).comap
      (MulAut.conjNormal (u*w*v)).toMonoidHom = ⊥ ↔
    derivedPositive m ⊓ (derivedPositive m).comap
      (MulAut.conjNormal w).toMonoidHom = ⊥ :=
  comap_intersection_mul_eq_bot_iff
    (MulAut.conjNormal : originalModelFixed m →* MulAut (commutator (originalModelFixed m)))
    (derivedPositive m) u w v
    (normal_comap_invariant (commutator (originalModelFixed m)) (fixedPositive m) u hu)
    (normal_comap_invariant (commutator (originalModelFixed m)) (fixedPositive m) v hv)

theorem positive_intersection_cell_eq_bot_iff (m : ℕ) (u w v : originalModelFixed m)
    (hu : u ∈ fixedPositive m) (hv : v ∈ fixedPositive m) :
    fixedPositive m ⊓ (fixedPositive m).comap (MulAut.conj (u*w*v)).toMonoidHom = ⊥ ↔
      fixedPositive m ⊓ (fixedPositive m).comap (MulAut.conj w).toMonoidHom = ⊥ :=
  comap_intersection_mul_eq_bot_iff (MulAut.conj) (fixedPositive m) u w v
    (fun x => (((fixedPositive m).le_normalizer hu) x).symm)
    (fun x => (((fixedPositive m).le_normalizer hv) x).symm)

theorem longest_intersection_eq_bot (m : ℕ) :
    shortPositiveIntersection m (15 : Fin 16) = ⊥ := by
  apply Subgroup.card_eq_one.mp
  have h := shortPositiveIntersection_card_factorization m (15 : Fin 16)
  rw [fixedPositive_card] at h
  have hw : inversionWeight (15 : Fin 16) = 12 := by decide
  rw [hw] at h
  have hq : 0 < (2^(2*m+1))^12 := pow_pos (pow_pos (by decide) _) _
  apply Nat.eq_of_mul_eq_mul_right hq
  exact h.symm.trans (one_mul _).symm

theorem full_intersection_bot_of_derived_bot (g : originalModelFixed 0)
    (h : derivedPositive 0 ⊓ (derivedPositive 0).comap (MulAut.conjNormal g).toMonoidHom = ⊥) :
    fixedPositive 0 ⊓ (fixedPositive 0).comap (MulAut.conj g).toMonoidHom = ⊥ := by
  obtain ⟨u, d, i, v, he⟩ := exists_short_fixed_cell 0 g
  have hd : d.val = 1 := by
    have hb : d.val ∈ (⊥ : Subgroup (originalModelFixed 0)) :=
      (le_of_eq fixedDiagonal_zero_eq_bot) d.property
    exact Subgroup.mem_bot.mp hb
  have he' : g = u.val * shortModelWord 0 i * v.val := by
    simpa only [hd, mul_one] using he
  have hs : shortDerivedIntersection 0 i = ⊥ :=
    (derived_shortIntersection_eq 0 i).trans
      ((cell_iff_of_eq
        (MulAut.conjNormal : originalModelFixed 0 →* MulAut (commutator (originalModelFixed 0)))
        (derivedPositive 0) g u.val (shortModelWord 0 i) v.val he'
        (normal_comap_invariant (commutator (originalModelFixed 0)) (fixedPositive 0)
          u.val u.property)
        (normal_comap_invariant (commutator (originalModelFixed 0)) (fixedPositive 0)
          v.val v.property)).mp h)
  have hi : i = (15 : Fin 16) := by
    by_contra hne
    exact non_opposite_derived_intersection_ne_bot i hne hs
  have hw : fixedPositive 0 ⊓ (fixedPositive 0).comap
      (MulAut.conj (shortModelWord 0 i)).toMonoidHom = ⊥ :=
    (congrArg (shortPositiveIntersection 0) hi).trans (longest_intersection_eq_bot 0)
  exact (cell_iff_of_eq (MulAut.conj) (fixedPositive 0)
    g u.val (shortModelWord 0 i) v.val he'
    (fun x => (((fixedPositive 0).le_normalizer u.property) x).symm)
    (fun x => (((fixedPositive 0).le_normalizer v.property) x).symm)).mpr hw

theorem full_opposite_conjugate_by_positive (g : originalModelFixed 0)
    (h : derivedPositive 0 ⊓ (derivedPositive 0).map (MulAut.conjNormal g).toMonoidHom = ⊥) :
    ∃ b ∈ fixedPositive 0,
      (fixedPositive 0).map (MulAut.conj g).toMonoidHom =
        (fixedNegative 0).map (MulAut.conj b).toMonoidHom := by
  have hc : derivedPositive 0 ⊓ (derivedPositive 0).comap
      (MulAut.conjNormal (g⁻¹)).toMonoidHom = ⊥ :=
    (congrArg (fun T : Subgroup (commutator (originalModelFixed 0)) => derivedPositive 0 ⊓ T)
      (map_eq_comap_inverse (MulAut.conjNormal) (derivedPositive 0) g)).symm.trans h
  have hf := full_intersection_bot_of_derived_bot (g⁻¹) hc
  have hfull : fixedPositive 0 ⊓ (fixedPositive 0).map (MulAut.conj g).toMonoidHom = ⊥ :=
    (congrArg (fun T : Subgroup (originalModelFixed 0) => fixedPositive 0 ⊓ T)
      (map_eq_comap_inverse (MulAut.conj) (fixedPositive 0) g)).trans hf
  exact fixed_opposite_conjugate_by_positive 0 g hfull

theorem derived_opposite_conjugate_by_positive (g : originalModelFixed 0)
    (h : derivedPositive 0 ⊓ (derivedPositive 0).map (MulAut.conjNormal g).toMonoidHom = ⊥) :
    ∃ b ∈ fixedPositive 0,
      (derivedPositive 0).map (MulAut.conjNormal g).toMonoidHom =
        ((fixedNegative 0).comap (commutator (originalModelFixed 0)).subtype).map
          (MulAut.conjNormal b).toMonoidHom := by
  obtain ⟨b, hb, he⟩ := full_opposite_conjugate_by_positive g h
  refine ⟨b, hb, ?_⟩
  have hh := congrArg (fun T : Subgroup (originalModelFixed 0) =>
    T.comap (commutator (originalModelFixed 0)).subtype) he
  exact (normal_comap_conjugate (commutator (originalModelFixed 0)) (fixedPositive 0) g).symm.trans
    (hh.trans (normal_comap_conjugate (commutator (originalModelFixed 0)) (fixedNegative 0) b))

end SymmetricSubgroupAsymptotics.CFSGReeFFourBinaryOppositePosition
