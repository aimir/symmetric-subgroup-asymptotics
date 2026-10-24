import SymmetricSubgroupAsymptotics.CFSGTwistedE6HeisenbergFixedPairing
import SymmetricSubgroupAsymptotics.CFSGTwistedE6SignedArrayCoordinates
import SymmetricSubgroupAsymptotics.CFSGQuadraticSignedTracePairing

/-! Nondegeneracy of the actual descended E6 cocycle.  Symmetrizing a
literal array, rather than lifting an abstract fixed quotient, supplies
all test vectors.  The signed quadratic trace is surjective in every
characteristic, including two. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics.CFSGTwistedE6FixedArrayNondegeneracy
open CFSGSerreOrdinaryTwists CFSGTwistedANaturalMatrices CFSGTwistedA2FixedField
open CFSGHeisenbergCoordinateGroup CFSGCommutingParameterTwist
open CFSGTwistedE6HeisenbergStableRootFamilies CFSGTwistedE6HeisenbergCoordinateTwist
open CFSGTwistedE6HeisenbergTwistCompatibility CFSGTwistedE6HeisenbergFixedPairing
open CFSGTwistedE6SignedArrayCoordinates CFSGQuadraticSignedFixedCoordinates
open CFSGQuadraticTracePairing CFSGQuadraticSignedTracePairing

theorem firstCoefficient_involutive (q : CFSG.PrimePower) :
    Function.Involutive (coefficientMap (definingFieldAutomorphism q 2) partner firstWeight) := by
  intro v
  have hh := congrArg (fun z : Element (q.Extension 2) 10 => z.a)
    (coordinateTwist_involutive (q.Extension 2) (definingFieldAutomorphism q 2)
      (fun x => extension_two_pow_twice q x) (⟨v, 0, 0⟩ : Element (q.Extension 2) 10))
  exact hh

theorem secondCoefficient_involutive (q : CFSG.PrimePower) :
    Function.Involutive (coefficientMap (definingFieldAutomorphism q 2) partner secondWeight) := by
  intro v
  have hh := congrArg (fun z : Element (q.Extension 2) 10 => z.b)
    (coordinateTwist_involutive (q.Extension 2) (definingFieldAutomorphism q 2)
      (fun x => extension_two_pow_twice q x) (⟨0, v, 0⟩ : Element (q.Extension 2) 10))
  exact hh

theorem signedTrace_surjective (q : CFSG.PrimePower) (c : signedLine q centralWeight) :
    ∃ z : q.Extension 2,
      z + (centralWeight : q.Extension 2) * definingFieldAutomorphism q 2 z = c.val := by
  obtain ⟨t, ht⟩ := traceLinear_surjective q 1
  have ht' : t + definingFieldAutomorphism q 2 t = 1 :=
    congrArg (fun x : fixedField q => (x : q.Extension 2)) ht
  have hc : definingFieldAutomorphism q 2 c.val = (centralWeight : q.Extension 2) * c.val :=
    c.property
  have hs : (centralWeight : q.Extension 2) * (centralWeight : q.Extension 2) = 1 := by
    rcases centralWeight_unit with h | h <;> simp only [h, Int.cast_one, Int.cast_neg] <;> ring
  refine ⟨c.val * t, ?_⟩
  rw [map_mul, hc]
  calc
    c.val * t + (centralWeight : q.Extension 2) *
        ((centralWeight : q.Extension 2) * c.val * definingFieldAutomorphism q 2 t) =
      c.val * t + ((centralWeight : q.Extension 2) * (centralWeight : q.Extension 2)) *
        (c.val * definingFieldAutomorphism q 2 t) := by ring
    _ = c.val * (t + definingFieldAutomorphism q 2 t) := by rw [hs]; ring
    _ = c.val := by rw [ht', mul_one]

private theorem dot_comm {L : Type*} [CommRing L] (a b : Fin 10 → L) :
    dot a b = dot b a := by
  apply Finset.sum_congr rfl
  intro i _
  exact mul_comm _ _

private theorem exists_dot {L : Type*} [Field L] (a : Fin 10 → L) (ha : a ≠ 0) (z : L) :
    ∃ v : Fin 10 → L, dot v a = z := by
  have hi : ∃ i, a i ≠ 0 := by
    by_contra h
    apply ha
    funext i
    exact not_not.mp (not_exists.mp h i)
  obtain ⟨i, hi⟩ := hi
  refine ⟨Pi.single i (z / a i), ?_⟩
  simpa [dot, Pi.single_apply, ite_mul] using (div_mul_cancel₀ z hi)

private theorem symmetrize_fixed {L : Type*} [AddCommGroup L] (t : L →+ L)
    (ht : Function.Involutive t) (v : L) : t (v + t v) = v + t v := by
  rw [map_add, ht]
  exact add_comm _ _

theorem exists_second_pairing (q : CFSG.PrimePower)
    (a : arraySpace q firstWeight) (ha : a.val ≠ 0) (c : signedLine q centralWeight) :
    ∃ b : arraySpace q secondWeight, dot b.val a.val = c.val := by
  obtain ⟨z, hz⟩ := signedTrace_surjective q c
  obtain ⟨v, hv⟩ := exists_dot a.val ha z
  let t := coefficientMap (definingFieldAutomorphism q 2) partner secondWeight
  have hb : v + t v ∈ arraySpace q secondWeight :=
    (mem_arraySpace_iff q secondWeight _).mpr
      (symmetrize_fixed t (secondCoefficient_involutive q) v)
  refine ⟨⟨v + t v, hb⟩, ?_⟩
  have ha' := (mem_arraySpace_iff q firstWeight a.val).mp a.property
  have hh := dot_twist (q.Extension 2) (definingFieldAutomorphism q 2) v a.val
  rw [ha', hv] at hh
  change dot (v + t v) a.val = c.val
  calc
    dot (v + t v) a.val = dot v a.val + dot (t v) a.val := by
      simp only [dot, Pi.add_apply, add_mul, Finset.sum_add_distrib]
    _ = z + (centralWeight : q.Extension 2) * definingFieldAutomorphism q 2 z :=
      congrArg₂ (fun x y : q.Extension 2 => x + y) hv hh
    _ = c.val := hz

theorem exists_first_pairing (q : CFSG.PrimePower)
    (b : arraySpace q secondWeight) (hb : b.val ≠ 0) (c : signedLine q centralWeight) :
    ∃ a : arraySpace q firstWeight, dot b.val a.val = c.val := by
  obtain ⟨z, hz⟩ := signedTrace_surjective q c
  obtain ⟨v, hv⟩ := exists_dot b.val hb z
  let t := coefficientMap (definingFieldAutomorphism q 2) partner firstWeight
  have ha : v + t v ∈ arraySpace q firstWeight :=
    (mem_arraySpace_iff q firstWeight _).mpr
      (symmetrize_fixed t (firstCoefficient_involutive q) v)
  refine ⟨⟨v + t v, ha⟩, ?_⟩
  have hb' := (mem_arraySpace_iff q secondWeight b.val).mp b.property
  have hh := dot_twist (q.Extension 2) (definingFieldAutomorphism q 2) b.val v
  rw [hb', dot_comm b.val v, hv] at hh
  have hv' : dot b.val v = z := (dot_comm b.val v).trans hv
  change dot b.val (v + t v) = c.val
  calc
    dot b.val (v + t v) = dot b.val v + dot b.val (t v) := by
      simp only [dot, Pi.add_apply, mul_add, Finset.sum_add_distrib]
    _ = z + (centralWeight : q.Extension 2) * definingFieldAutomorphism q 2 z :=
      congrArg₂ (fun x y : q.Extension 2 => x + y) hv' hh
    _ = c.val := hz

end SymmetricSubgroupAsymptotics.CFSGTwistedE6FixedArrayNondegeneracy
