import SymmetricSubgroupAsymptotics.CFSGTwistedDFixedCentralCocycle
import SymmetricSubgroupAsymptotics.CFSGOrthogonalDCenterPrimeCoprime
import SymmetricSubgroupAsymptotics.CFSGCentralCocyclePGroup

/-! Actual defining-characteristic p-subgroups above the ORIGINAL fixed
action image consist of literal fixed natural matrices. Coprime actual
centre order cancels the proved central difference; no fixed lift is
assumed for arbitrary elements. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGTwistedDFixedPSubgroups
open CFSGOrthogonalDSerreMatrices CFSGTwistedDFixedCentralCocycle
open CFSGTwistedDNaturalFieldTwist CFSGSerreOrdinaryTwists

theorem pSubgroup_fixed (s : ℕ) (q : CFSG.PrimePower)
    (L : Subgroup (elementaryRootGroup (q.Extension 2) (s + 4)))
    (hL : IsPGroup q.prime L) (hLP : L ≤ naturalFixedPreimage s q) :
    ∀ u : L, naturalAutomorphism (q.Extension 2) (s + 2)
      (definingFieldAutomorphism q 2) u.val = u.val :=
  CFSGCentralCocyclePGroup.fixed_on_pSubgroup_of_central_difference
    (naturalAutomorphism (q.Extension 2) (s + 2) (definingFieldAutomorphism q 2)) L hL
    (fun u => naturalFixedPreimage_central_difference s q u.val (hLP u.property))
    (CFSGOrthogonalDCenterPrimeCoprime.center_prime_coprime (q.Extension 2) s q.prime)

theorem pSubgroup_unit_fixed (s : ℕ) (q : CFSG.PrimePower)
    (L : Subgroup (elementaryRootGroup (q.Extension 2) (s + 4)))
    (hL : IsPGroup q.prime L) (hLP : L ≤ naturalFixedPreimage s q) (u : L) :
    unitTwist (q.Extension 2) (s + 2) (definingFieldAutomorphism q 2) u.val.val = u.val.val :=
  congrArg Subtype.val (pSubgroup_fixed s q L hL hLP u)

theorem pSubgroup_matrix_fixed (s : ℕ) (q : CFSG.PrimePower)
    (L : Subgroup (elementaryRootGroup (q.Extension 2) (s + 4)))
    (hL : IsPGroup q.prime L) (hLP : L ≤ naturalFixedPreimage s q) (u : L) :
    matrixTwist (q.Extension 2) (s + 2) (definingFieldAutomorphism q 2)
      (u.val.val : Mat (q.Extension 2) (s + 4)) = (u.val.val : Mat (q.Extension 2) (s + 4)) :=
  congrArg (fun a : (Mat (q.Extension 2) (s + 4))ˣ => (a : Mat (q.Extension 2) (s + 4)))
    (pSubgroup_unit_fixed s q L hL hLP u)

end SymmetricSubgroupAsymptotics.CFSGTwistedDFixedPSubgroups
