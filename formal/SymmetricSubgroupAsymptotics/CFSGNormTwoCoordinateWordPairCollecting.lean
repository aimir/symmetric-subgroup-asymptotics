import SymmetricSubgroupAsymptotics.CFSGNormTwoCoordinatePositivePairCollecting

/-! Actual conjugation of a positive A2 pair by any original Weyl word.
The same integral unit commutator coefficient works in every ring, so
mixed-sign A2 pairs require no lifting or characteristic restriction. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGNormTwoCoordinateWordPairCollecting
open CFSGIntegerMatrixPairing CFSGNormTwoRootPairing CFSGSerreQuadraticMatrix
open CFSGNormTwoGeckIntegralRealization CFSGNormTwoGeckWeylLatticeLinear
open CFSGNormTwoGeckWeylWordDegree CFSGNormTwoCoordinateRootSubgroup
open CFSGSerreQuadraticWeylWord CFSGNormTwoCoordinateSelectedRootElement
open CFSGNormTwoCoordinatePositivePairOrbit CFSGNormTwoCoordinateWordRootElementSign
open CFSGNormTwoCoordinateSimpleRootParametrization CFSGNormTwoCoordinateRaisedRoot
open CFSGNormTwoCoordinateSignedRootCollecting CFSGNormTwoCoordinateRootCollectingTransport

variable {r : ℕ} (A : Matrix (Fin r) (Fin r) ℤ) (hd : ∀i,A i i=2)
    (hs : A.transpose=A) (hp : (rationalMatrix A).PosDef)
    (ho : ∀i j,i≠j→A i j≤0)
    [Fintype (Roots A)] [DecidableEq (Roots A)]
    [(rootPairing A hs hp).IsReduced] [(rootPairing A hs hp).IsIrreducible]

local notation "b₀" => coordinateBase A hd hs hp ho
local notation "s₀" => coordinateIndexEquiv A hd hs hp ho
local notation "D" => realizationData A hs hp b₀ s₀
private abbrev CoordMat (K : Type) := Matrix ((b₀).support⊕Roots A) ((b₀).support⊕Roots A) K

open CFSGNormTwoCoordinatePositivePairCollecting

private theorem sign_mul {a b : ℤ} (ha : a = 1 ∨ a = -1) (hb : b = 1 ∨ b = -1) :
    a * b = 1 ∨ a * b = -1 := by
  rcases ha with rfl | rfl <;> rcases hb with rfl | rfl <;> norm_num

 theorem word_pair_commutator_sign (w : List (Fin r)) (k l : Roots A)
    (hk : ∀ t, 0 ≤ k.val t) (hl : ∀ t, 0 ≤ l.val t)
    (hpair : integerPairing A k.val l.val = -1) :
    ∃ ε : ℤ, (ε = 1 ∨ ε = -1) ∧ ∀ (K : Type) [CommRing K] (a b : K),
      selectedRootElement A hd hs hp ho K (wordRoot A hs hp b₀ s₀ w k) a *
        selectedRootElement A hd hs hp ho K (wordRoot A hs hp b₀ s₀ w l) b *
        (selectedRootElement A hd hs hp ho K (wordRoot A hs hp b₀ s₀ w k) a)⁻¹ *
        (selectedRootElement A hd hs hp ho K (wordRoot A hs hp b₀ s₀ w l) b)⁻¹ =
      selectedRootElement A hd hs hp ho K
        (wordRoot A hs hp b₀ s₀ w (sumRoot A hs k l hpair)) ((ε : K) * (a * b)) := by
  obtain ⟨ε, hε, he⟩ := positive_pair_commutator_sign A hd hs hp ho k l hk hl hpair
  obtain ⟨x, hx, hxword⟩ := word_selected_root_sign A hd hs hp ho w k
  obtain ⟨y, hy, hyword⟩ := word_selected_root_sign A hd hs hp ho w l
  obtain ⟨z, hz, hzword⟩ := word_selected_root_sign A hd hs hp ho w (sumRoot A hs k l hpair)
  refine ⟨z * ε * x * y, sign_mul (sign_mul (sign_mul hz hε) hx) hy, ?_⟩
  intro K _ a b
  let φ : MulAut ((CoordMat A hd hs hp ho K)ˣ) := MulAut.conj (canonicalWord D K w)
  have hxx : (x : K) * (x : K) = 1 := by rcases hx with rfl | rfl <;> norm_num
  have hyy : (y : K) * (y : K) = 1 := by rcases hy with rfl | rfl <;> norm_num
  have hka : φ (selectedRootElement A hd hs hp ho K k ((x : K) * a)) =
      selectedRootElement A hd hs hp ho K (wordRoot A hs hp b₀ s₀ w k) a := by
    change canonicalWord D K w * _ * (canonicalWord D K w)⁻¹ = _
    rw [hxword, ← mul_assoc, hxx, one_mul]
  have hlb : φ (selectedRootElement A hd hs hp ho K l ((y : K) * b)) =
      selectedRootElement A hd hs hp ho K (wordRoot A hs hp b₀ s₀ w l) b := by
    change canonicalWord D K w * _ * (canonicalWord D K w)⁻¹ = _
    rw [hyword, ← mul_assoc, hyy, one_mul]
  calc
    _ = φ (selectedRootElement A hd hs hp ho K k ((x : K) * a) *
        selectedRootElement A hd hs hp ho K l ((y : K) * b) *
        (selectedRootElement A hd hs hp ho K k ((x : K) * a))⁻¹ *
        (selectedRootElement A hd hs hp ho K l ((y : K) * b))⁻¹) := by
      simp only [map_mul, map_inv, hka, hlb]
    _ = φ (selectedRootElement A hd hs hp ho K (sumRoot A hs k l hpair)
        ((ε : K) * (((x : K) * a) * ((y : K) * b)))) :=
      congrArg φ (he K ((x : K) * a) ((y : K) * b))
    _ = selectedRootElement A hd hs hp ho K
        (wordRoot A hs hp b₀ s₀ w (sumRoot A hs k l hpair))
          ((z : K) * ((ε : K) * (((x : K) * a) * ((y : K) * b)))) := hzword K _
    _ = _ := by
      congr 1
      simp only [Int.cast_mul]
      ring

end SymmetricSubgroupAsymptotics.CFSGNormTwoCoordinateWordPairCollecting
