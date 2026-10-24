import SymmetricSubgroupAsymptotics.CFSGNormTwoCoordinateSignedRootCollecting
import SymmetricSubgroupAsymptotics.CFSGNormTwoCoordinateRootPairCommute
import Mathlib.Tactic.Group

/-! A simple positive parameter acts on an actual selected root parameter
by the genuine two-factor A2 collecting law in characteristic two. The
integral sign is removed by characteristic two, not by changing root words. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGNormTwoCoordinateCharTwoSimpleConjugation
open CFSGIntegerMatrixPairing CFSGNormTwoRootPairing CFSGSerreQuadraticMatrix
open CFSGNormTwoGeckIntegralRealization CFSGNormTwoCoordinateSelectedRootElement
open CFSGNormTwoCoordinateSignedRootCollecting CFSGNormTwoCoordinateRaisedRoot
open CFSGNormTwoCoordinateRootCollectingTransport
variable {r : ℕ} (A : Matrix (Fin r) (Fin r) ℤ) (hd : ∀ i,A i i=2)
  (hs : A.transpose=A) (hp : (rationalMatrix A).PosDef)
  (ho : ∀ i j,i≠j→A i j≤0)
  [Fintype (Roots A)] [DecidableEq (Roots A)]
  [(rootPairing A hs hp).IsReduced] [(rootPairing A hs hp).IsIrreducible]
local notation "b₀" => coordinateBase A hd hs hp ho
local notation "s₀" => coordinateIndexEquiv A hd hs hp ho
local notation "D" => realizationData A hs hp b₀ s₀
private abbrev U (K : Type) [CommRing K] :=
  (Matrix ((b₀).support⊕Roots A) ((b₀).support⊕Roots A) K)ˣ
private abbrev root (K : Type) [CommRing K] (k : Roots A) (t : K) : U A hd hs hp ho K :=
  selectedRootElement A hd hs hp ho K k t
private abbrev simple (K : Type) [CommRing K] (i : Fin r) (a : K) : U A hd hs hp ho K :=
  canonicalRoot D K false i a

theorem simple_positive_conjugate (K : Type) [CommRing K] [CharP K 2]
    (k : Roots A) (hk : ∀ j,0≤k.val j) (i : Fin r)
    (hpair : integerPairing A k.val (s₀ i : Roots A).val= -1) (a t : K) :
    simple A hd hs hp ho K i a * root A hd hs hp ho K k t *
        (simple A hd hs hp ho K i a)⁻¹ =
      root A hd hs hp ho K k t *
        root A hd hs hp ho K (raisedRoot A hd hs hp ho k i hpair) (a*t) := by
  obtain ⟨e,he,hcomm⟩ := simple_positive_commutator_sign A hd hs hp ho k hk i hpair
  have hsign : (e : K)=1 := by
    rcases he with rfl | rfl <;> simp only [Int.cast_one,Int.cast_neg,CharTwo.neg_eq]
  have hc := hcomm K a t
  rw [hsign,one_mul,mul_comm t a] at hc
  change simple A hd hs hp ho K i a * root A hd hs hp ho K k t *
      (simple A hd hs hp ho K i a)⁻¹ * (root A hd hs hp ho K k t)⁻¹ =
    root A hd hs hp ho K (raisedRoot A hd hs hp ho k i hpair) (a*t) at hc
  have hraised : integerPairing A k.val
      (raisedRoot A hd hs hp ho k i hpair).val=1 := by
    rw [raisedRoot_val,map_add,k.property,hpair]
    norm_num
  have hxy : Commute (root A hd hs hp ho K k t)
      (root A hd hs hp ho K (raisedRoot A hd hs hp ho k i hpair) (a*t)) :=
    CFSGNormTwoCoordinateRootPairCommute.pair_commute A hd hs hp ho K k
      (raisedRoot A hd hs hp ho k i hpair) (Or.inr hraised) t (a*t)
  calc
    _ = (simple A hd hs hp ho K i a * root A hd hs hp ho K k t *
        (simple A hd hs hp ho K i a)⁻¹ * (root A hd hs hp ho K k t)⁻¹) *
          root A hd hs hp ho K k t := by group
    _ = root A hd hs hp ho K (raisedRoot A hd hs hp ho k i hpair) (a*t) *
        root A hd hs hp ho K k t := by rw [hc]
    _ = _ := hxy.eq.symm

end SymmetricSubgroupAsymptotics.CFSGNormTwoCoordinateCharTwoSimpleConjugation
