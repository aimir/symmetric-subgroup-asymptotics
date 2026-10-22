import SymmetricSubgroupAsymptotics.CFSGSerrePairedFixedRoots
import SymmetricSubgroupAsymptotics.CFSGTwistedDFixedA2
import SymmetricSubgroupAsymptotics.CFSGTwistedDNaturalFork
import SymmetricSubgroupAsymptotics.CFSGTwistedAPairedFixedRoots

/-! The exchanged D fork supplies genuine paired fixed root words in
the ORIGINAL source, for arbitrary extension-field parameters and both
signs. Derived membership remains a separate word calculation. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGTwistedDPairedFixedRoots
open CFSG.Models.Chevalley CFSGSerreModelRootGeneration CFSGTwistedDFixedA2
open CFSGOrthogonalDGenerationForkTorus CFSGTwistedDNaturalFork

theorem fork_cartan_zero (s : ℕ) :
    CartanMatrix.D (s + 4) (pen (s + 2)) (last (s + 2)) = 0 := by
  have hne : pen (s + 2) ≠ last (s + 2) := pen_ne_last (s + 2)
  simp only [CartanMatrix.D, Matrix.of_apply, if_neg hne]
  simp [pen, last]

theorem fork_orbit_cartan_zero (s : ℕ) :
    CartanMatrix.D (s + 4) (pen (s + 2)) (CFSG.Models.dTwist (pen (s + 2))) = 0 := by
  rw [twist_pen]
  exact fork_cartan_zero s

def pairedFork (s : ℕ) (q : CFSG.PrimePower) (neg : Bool) (t : q.Extension 2) : Fixed s q :=
  CFSGSerrePairedFixedRoots.pairedFixedRoot (CartanMatrix.D (s + 4)) (q.Extension 2)
    CFSG.Models.dTwist (fun _ => q.order) neg (pen (s + 2)) (fork_orbit_cartan_zero s)
    (CFSGSerreDiagram.dTwist_involutive (s + 4) _) t
    (CFSGTwistedANaturalMatrices.extension_two_pow_twice q t)

theorem pairedFork_toModel (s : ℕ) (q : CFSG.PrimePower) (neg : Bool) (t : q.Extension 2) :
    toModel s q (pairedFork s q neg t) =
      modelRoot (CartanMatrix.D (s + 4)) (q.Extension 2) neg (pen (s + 2)) t *
        modelRoot (CartanMatrix.D (s + 4)) (q.Extension 2) neg (last (s + 2)) (t ^ q.order) := by
  change modelRoot (CartanMatrix.D (s + 4)) (q.Extension 2) neg (pen (s + 2)) t *
    modelRoot (CartanMatrix.D (s + 4)) (q.Extension 2) neg
      (CFSG.Models.dTwist (pen (s + 2))) (t ^ q.order) = _
  rw [twist_pen]

end SymmetricSubgroupAsymptotics.CFSGTwistedDPairedFixedRoots
