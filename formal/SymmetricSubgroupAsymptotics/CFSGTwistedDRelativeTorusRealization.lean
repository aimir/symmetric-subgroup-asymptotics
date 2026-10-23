import SymmetricSubgroupAsymptotics.CFSGTwistedDRelativeTorusIndex
import SymmetricSubgroupAsymptotics.CFSGTwistedDDerivedNegativePairedRoots
import SymmetricSubgroupAsymptotics.CFSGOrthogonalDOrthogonalRootCommutation
import SymmetricSubgroupAsymptotics.CFSGOrthogonalDCommutingNodeTori

/-! The actual paired torus lies above the original Derived action image.
Its literal positive diagonal entries are precisely the two checked
relative torus parameters, including the norm-one factor. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGTwistedDRelativeTorusRealization
open CFSGOrthogonalDSerreMatrices CFSGOrthogonalDGenerationForkTorus
open CFSGTwistedDPairedRootImages CFSGTwistedDPairedTorusImages
open CFSGTwistedDPairedTorusAction CFSGTwistedDDerivedPairedRoots
open CFSGTwistedDDerivedNegativePairedRoots CFSGTwistedDRelativeTorusParameters
open CFSGTwistedA2FixedField CFSGSerreOrdinaryTwists
open CFSGOrthogonalDBinaryElements CFSGOrthogonalDForkNodeTori CFSGTwistedDPairedTorusWords

private theorem map_mem_of_eq {G H : Type*} [Group G] [Group H]
    (f : G →* H) (P : Subgroup G) (g : G) (h : H)
    (hg : g ∈ P) (he : f g = h) : h ∈ P.map f :=
  ⟨g, hg, he⟩

def retainedUnitSubgroup (s : ℕ) (q : CFSG.PrimePower) :
    Subgroup ((Mat (q.Extension 2) (s + 4))ˣ) :=
  (naturalDerivedPreimage s q).map (elementaryRootGroup (q.Extension 2) (s + 4)).subtype

theorem pairedNaturalTorus_mem (s : ℕ) (q : CFSG.PrimePower) (c : (q.Extension 2)ˣ) :
    (pairedNaturalTorus s q c).val ∈ retainedUnitSubgroup s q := by
  have ht := CFSGOrthogonalDCommutingNodeTori.nodeTorus_pair_mem
    (q.Extension 2) (s + 2) (naturalDerivedPreimage s q)
    (pen (s + 2)) (last (s + 2)) (definingFieldAutomorphism q 2).toRingHom c
    (fun e f a b => CFSGOrthogonalDOrthogonalRootCommutation.rootElement_commute
      (q.Extension 2) (s + 4) (by omega) (pen (s + 2)) (last (s + 2))
      (pen_ne_last (s + 2)) (CFSGTwistedDPairedFixedRoots.fork_cartan_zero s) e f a b)
    (by
      intro e a
      have hm : pairedNaturalRoot s q e a ∈ naturalDerivedPreimage s q := by
        cases e
        · exact paired_mem_derived_preimage s q a
        · exact paired_negative_mem_derived_preimage s q a
      change rootElement (q.Extension 2) (s + 4) e (pen (s + 2)) a *
        rootElement (q.Extension 2) (s + 4) e (last (s + 2))
          (definingFieldAutomorphism q 2 a) ∈ naturalDerivedPreimage s q
      simpa only [definingFieldAutomorphism_apply] using hm)
  exact map_mem_of_eq (elementaryRootGroup (q.Extension 2) (s + 4)).subtype
    (naturalDerivedPreimage s q) (pairedNaturalTorus s q c)
    (pairedNaturalTorus s q c).val ht rfl

theorem quotientHom_val (q : CFSG.PrimePower) (c : (q.Extension 2)ˣ) :
    ((quotientHom q c).val : q.Extension 2) =
      definingFieldAutomorphism q 2 (c : q.Extension 2) * (c : q.Extension 2)⁻¹ := by
  change ((unitFrobenius q c * c⁻¹ : (q.Extension 2)ˣ) : q.Extension 2) = _
  rw [Units.val_mul, Units.val_inv_eq_inv_val, unitFrobenius_val]

theorem positive_pen_norm (s : ℕ) (q : CFSG.PrimePower) (c : (q.Extension 2)ˣ) :
    pairedDiagonal s q c (Sum.inl (pen (s + 2))) =
      (((normHom q c : (fixedField q)ˣ) : fixedField q) : q.Extension 2) := by
  rw [(pairedDiagonal_values s q c).1, normHom_val, frobeniusUnit_val,
    definingFieldAutomorphism_apply]

theorem positive_last_quotient (s : ℕ) (q : CFSG.PrimePower) (c : (q.Extension 2)ˣ) :
    pairedDiagonal s q c (Sum.inl (last (s + 2))) =
      ((quotientHom q c).val : q.Extension 2) := by
  rw [(pairedDiagonal_values s q c).2.1, quotientHom_val, frobeniusUnit_val,
    definingFieldAutomorphism_apply, mul_comm]

end SymmetricSubgroupAsymptotics.CFSGTwistedDRelativeTorusRealization
