import SymmetricSubgroupAsymptotics.CFSGTwistedDPairedFixedRoots
import SymmetricSubgroupAsymptotics.CFSGSerreOrthogonalNodeCommutation
import SymmetricSubgroupAsymptotics.CFSGCommutingPairedWord

/-! The actual original paired fixed torus word separates into two
orthogonal-node words. No rank-one identity or root additivity on the
original Serre source is asserted; natural images are computed later. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGTwistedDPairedTorusWords
open CFSG.Models.Chevalley CFSGSerreModelRootGeneration CFSGTwistedDFixedA2
open CFSGTwistedDPairedFixedRoots CFSGOrthogonalDGenerationForkTorus

def wordSign : Fin 4 → Bool := ![false, true, false, true]

def wordParameter {K : Type} [Field K] (c : Kˣ) : Fin 4 → K :=
  ![(c : K) - 1, 1, (c : K)⁻¹ - 1, -(c : K)]

def nodeWord (s : ℕ) (q : CFSG.PrimePower) (i : Fin (s + 4))
    (t : Fin 4 → q.Extension 2) : Model (CartanMatrix.D (s + 4)) (q.Extension 2) :=
  modelRoot (CartanMatrix.D (s + 4)) (q.Extension 2) (wordSign 0) i (t 0) *
    modelRoot (CartanMatrix.D (s + 4)) (q.Extension 2) (wordSign 1) i (t 1) *
    modelRoot (CartanMatrix.D (s + 4)) (q.Extension 2) (wordSign 2) i (t 2) *
    modelRoot (CartanMatrix.D (s + 4)) (q.Extension 2) (wordSign 3) i (t 3)

def pairedTorus (s : ℕ) (q : CFSG.PrimePower) (c : (q.Extension 2)ˣ) : Fixed s q :=
  pairedFork s q false ((c : q.Extension 2) - 1) * pairedFork s q true 1 *
    pairedFork s q false ((c : q.Extension 2)⁻¹ - 1) * pairedFork s q true (-(c : q.Extension 2))

theorem pairedTorus_toModel (s : ℕ) (q : CFSG.PrimePower) (c : (q.Extension 2)ˣ) :
    toModel s q (pairedTorus s q c) =
      nodeWord s q (pen (s + 2)) (wordParameter c) *
        nodeWord s q (last (s + 2)) (fun i => (wordParameter c i) ^ q.order) := by
  let a : Fin 4 → Model (CartanMatrix.D (s + 4)) (q.Extension 2) :=
    fun i => modelRoot (CartanMatrix.D (s + 4)) (q.Extension 2) (wordSign i)
      (pen (s + 2)) (wordParameter c i)
  let b : Fin 4 → Model (CartanMatrix.D (s + 4)) (q.Extension 2) :=
    fun i => modelRoot (CartanMatrix.D (s + 4)) (q.Extension 2) (wordSign i)
      (last (s + 2)) ((wordParameter c i) ^ q.order)
  have hc : ∀ i j, Commute (a i) (b j) := by
    intro i j
    exact CFSGSerreOrthogonalNodeCommutation.modelRoots_commute_all_signs
      (CartanMatrix.D (s + 4)) (q.Extension 2) (pen (s + 2)) (last (s + 2))
      (pen_ne_last (s + 2)) (fork_cartan_zero s) (wordSign i) (wordSign j) _ _
  simp only [pairedTorus, map_mul, pairedFork_toModel]
  change (a 0 * b 0) * (a 1 * b 1) * (a 2 * b 2) * (a 3 * b 3) =
    (a 0 * a 1 * a 2 * a 3) * (b 0 * b 1 * b 2 * b 3)
  exact CFSGCommutingPairedWord.four_pairs a b hc

end SymmetricSubgroupAsymptotics.CFSGTwistedDPairedTorusWords
