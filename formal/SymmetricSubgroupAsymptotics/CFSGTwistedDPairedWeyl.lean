import SymmetricSubgroupAsymptotics.CFSGTwistedDDerivedNegativePairedRoots
import SymmetricSubgroupAsymptotics.CFSGCommutingPairedWord
import SymmetricSubgroupAsymptotics.CFSGOrthogonalDOrthogonalRootCommutation

/-! The actual relative terminal Weyl word belongs to the same original
Derived preimage and separates into the two original orthogonal node
Weyl words. No fixed-group presentation is used. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGTwistedDPairedWeyl
open CFSGOrthogonalDSerreMatrices CFSGOrthogonalDGenerationForkTorus
open CFSGOrthogonalDBinaryElements CFSGTwistedDPairedRootImages
open CFSGTwistedDDerivedPairedRoots CFSGTwistedDDerivedNegativePairedRoots

def pairedWeyl (s : ℕ) (q : CFSG.PrimePower) : elementaryRootGroup (q.Extension 2) (s + 4) :=
  pairedNaturalRoot s q false (-1) * pairedNaturalRoot s q true 1 *
    pairedNaturalRoot s q false (-1)

theorem pairedWeyl_mem (s : ℕ) (q : CFSG.PrimePower) :
    pairedWeyl s q ∈ naturalDerivedPreimage s q :=
  (naturalDerivedPreimage s q).mul_mem
    ((naturalDerivedPreimage s q).mul_mem (paired_mem_derived_preimage s q (-1))
      (paired_negative_mem_derived_preimage s q 1)) (paired_mem_derived_preimage s q (-1))

theorem pairedWeyl_eq_nodes (s : ℕ) (q : CFSG.PrimePower) :
    pairedWeyl s q = simpleWeyl (q.Extension 2) (s + 4) (pen (s + 2)) *
      simpleWeyl (q.Extension 2) (s + 4) (last (s + 2)) := by
  let K := q.Extension 2
  let e : Fin 4 → Bool := ![false, true, false, false]
  let t : Fin 4 → K := ![-1, 1, -1, 0]
  let a : Fin 4 → elementaryRootGroup K (s + 4) :=
    fun i => rootElement K (s + 4) (e i) (pen (s + 2)) (t i)
  let b : Fin 4 → elementaryRootGroup K (s + 4) :=
    fun i => rootElement K (s + 4) (e i) (last (s + 2)) (t i)
  have hc (i j : Fin 4) : Commute (a i) (b j) :=
    CFSGOrthogonalDOrthogonalRootCommutation.rootElement_commute K (s + 4) (by omega)
      (pen (s + 2)) (last (s + 2)) (pen_ne_last (s + 2))
      (CFSGTwistedDPairedFixedRoots.fork_cartan_zero s) (e i) (e j) (t i) (t j)
  have hword := CFSGCommutingPairedWord.four_pairs a b hc
  have hm : (-1 : K) ^ q.order = -1 := by
    change CFSGSerreOrdinaryTwists.definingFieldAutomorphism q 2 (-1) = -1
    rw [map_neg, map_one]
  change (rootElement K (s + 4) false (pen (s + 2)) (-1) *
      rootElement K (s + 4) false (last (s + 2)) ((-1 : K) ^ q.order)) *
    (rootElement K (s + 4) true (pen (s + 2)) 1 *
      rootElement K (s + 4) true (last (s + 2)) (1 ^ q.order)) *
    (rootElement K (s + 4) false (pen (s + 2)) (-1) *
      rootElement K (s + 4) false (last (s + 2)) ((-1 : K) ^ q.order)) = _
  rw [hm, one_pow]
  simpa [a, b, e, t, simpleWeyl] using hword

end SymmetricSubgroupAsymptotics.CFSGTwistedDPairedWeyl
