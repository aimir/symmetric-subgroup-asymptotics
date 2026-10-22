import SymmetricSubgroupAsymptotics.CFSGTwistedDDerivedPairedRoots
import SymmetricSubgroupAsymptotics.CFSGTwistedDNegativeTorusAction

/-! Explicit ORIGINAL Fixed commutators supply every negative paired
natural root in the SAME Derived image. No source rank-one identity or
source transpose symmetry is used. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped commutatorElement
namespace SymmetricSubgroupAsymptotics.CFSGTwistedDDerivedNegativePairedRoots
open CFSG.Models.Chevalley CFSGSerreFixedRootElements CFSGTwistedDFixedA2
open CFSGOrthogonalDSerreMatrices CFSGTwistedDFixedCentralCocycle
open CFSGTwistedDPairedFixedRoots CFSGTwistedDPairedRootImages
open CFSGTwistedDPairedTorusWords CFSGTwistedDPairedTorusImages
open CFSGTwistedDPairedRootAdditivity CFSGTwistedDNegativeTorusAction
open CFSGTwistedDDerivedPairedRoots

private theorem rank_ge_four (s : ℕ) : 4 ≤ s + 4 := by omega

def negativeDerivedWord (s : ℕ) (q : CFSG.PrimePower) (c : (q.Extension 2)ˣ)
    (a : q.Extension 2) : Derived s q :=
  derivedCommutator (CartanMatrix.D (s + 4)) (q.Extension 2) CFSG.Models.dTwist
    (fun _ => q.order) (pairedTorus s q c) (pairedFork s q true a)

theorem negativeDerivedWord_coe (s : ℕ) (q : CFSG.PrimePower) (c : (q.Extension 2)ˣ)
    (a : q.Extension 2) :
    (negativeDerivedWord s q c a).val = ⁅pairedTorus s q c, pairedFork s q true a⁆ := rfl

theorem natural_negative_commutator (s : ℕ) (q : CFSG.PrimePower) (c : (q.Extension 2)ˣ)
    (a : q.Extension 2) :
    ⁅pairedNaturalTorus s q c, pairedNaturalRoot s q true a⁆ =
      pairedNaturalRoot s q true ((((c : q.Extension 2)⁻¹)^2 - 1) * a) := by
  rw [commutatorElement_def, paired_negative_conjugation, pairedNaturalRoot_inv,
    ← pairedNaturalRoot_add]
  congr 1
  ring

set_option maxRecDepth 4096 in
theorem negativeDerivedWord_image (s : ℕ) (q : CFSG.PrimePower) (c : (q.Extension 2)ˣ)
    (a : q.Extension 2) :
    CFSGTwistedDDerivedPairedRoots.derivedImageAction s q (negativeDerivedWord s q c a) =
      elementaryImageAction (q.Extension 2) (s + 4) (rank_ge_four s)
        (pairedNaturalRoot s q true ((((c : q.Extension 2)⁻¹)^2 - 1) * a)) := by
  let μ := CFSGTwistedDFixedCentralCocycle.fixedImageAction s q
  let ν : elementaryRootGroup (q.Extension 2) (s + 4) →*
      ((orthogonalBaseChange (q.Extension 2) (s + 4) (rank_ge_four s)).range ≃ₗ[q.Extension 2]
        (orthogonalBaseChange (q.Extension 2) (s + 4) (rank_ge_four s)).range) :=
    elementaryImageAction (q.Extension 2) (s + 4) (rank_ge_four s)
  rw [derivedImageAction_apply, negativeDerivedWord_coe]
  calc
    _ = ⁅μ (pairedTorus s q c), μ (pairedFork s q true a)⁆ := map_commutatorElement μ _ _
    _ = ⁅ν (pairedNaturalTorus s q c), ν (pairedNaturalRoot s q true a)⁆ := by
      rw [pairedTorus_image, paired_image]
      rfl
    _ = ν ⁅pairedNaturalTorus s q c, pairedNaturalRoot s q true a⁆ :=
      (map_commutatorElement ν _ _).symm
    _ = _ := congrArg ν (natural_negative_commutator s q c a)

theorem paired_negative_mem_derived_preimage (s : ℕ) (q : CFSG.PrimePower) (t : q.Extension 2) :
    pairedNaturalRoot s q true t ∈ naturalDerivedPreimage s q := by
  obtain ⟨c, hc⟩ := IsCyclic.exists_generator (α := (q.Extension 2)ˣ)
  have hcard : 4 ≤ Nat.card (q.Extension 2) := by
    rw [CFSGTwistedANaturalMatrices.extension_two_card]
    have hq : 2 ≤ q.order := q.prime_isPrime.two_le.trans
      (Nat.le_self_pow (Nat.ne_of_gt q.exponent_pos) q.prime)
    nlinarith
  have hd : ((c : q.Extension 2)⁻¹)^2 - 1 ≠ 0 := sub_ne_zero.mpr
    (by simpa only [Units.val_inv_eq_inv_val] using
      CFSGTypeAPrimitiveUnitSquare.inverse_square_ne_one hcard c hc)
  let a := t / (((c : q.Extension 2)⁻¹)^2 - 1)
  have ha : (((c : q.Extension 2)⁻¹)^2 - 1) * a = t := by
    dsimp only [a]
    exact mul_div_cancel₀ t hd
  refine ⟨negativeDerivedWord s q c a, ?_⟩
  simpa only [ha] using negativeDerivedWord_image s q c a

end SymmetricSubgroupAsymptotics.CFSGTwistedDDerivedNegativePairedRoots
