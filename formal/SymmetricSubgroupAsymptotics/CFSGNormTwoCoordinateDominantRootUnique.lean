import SymmetricSubgroupAsymptotics.CFSGNormTwoCoordinateDominantSupport
import SymmetricSubgroupAsymptotics.CFSGIntegralNormTwoSigns
import SymmetricSubgroupAsymptotics.CFSGNormTwoPairingBounds

/-! A positive dominant root in the actual irreducible coordinate
root system is unique. The argument uses the one-sign norm-two theorem,
not a selected exceptional root table or a chamber-recognition premise. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGNormTwoCoordinateDominantRootUnique
open CFSGIntegerMatrixPairing CFSGNormTwoRootPairing CFSGIntegerDominantSupport
open CFSGIntegerPairingPositiveDescent CFSGNormTwoCoordinateDominantSupport
open CFSGIntegralNormTwoSigns CFSGNormTwoPairingBounds
variable {r : ℕ} (A : Matrix (Fin r) (Fin r) ℤ) (hd : ∀i,A i i=2)
    (hs : A.transpose=A) (hp : (rationalMatrix A).PosDef)
    (ho : ∀i j,i≠j→A i j≤0)
    [Fintype (Roots A)] [DecidableEq (Roots A)]
    [(rootPairing A hs hp).IsReduced] [(rootPairing A hs hp).IsIrreducible]

include hs

theorem dominant_pair_nonneg (x y : Fin r→ℤ)
    (hdom : ∀i,0 ≤ integerPairing A x (Pi.single i (1:ℤ) : Fin r→ℤ))
    (hy : ∀i,0≤y i) : 0 ≤ integerPairing A x y := by
  rw [integer_symmetric A hs x y,pairing_coordinate_sum_left]
  apply Finset.sum_nonneg
  intro i hi
  rw [integer_symmetric A hs (Pi.single i (1:ℤ) : Fin r→ℤ) x]
  exact mul_nonneg (hy i) (hdom i)

include hd hp ho

theorem dominant_positive_pair_pos (k l : Roots A) (hk : ∀i,0≤k.val i)
    (hl : ∀i,0≤l.val i)
    (hkdom : ∀i,0 ≤ integerPairing A k.val (Pi.single i (1:ℤ) : Fin r→ℤ))
    (hldom : ∀i,0 ≤ integerPairing A l.val (Pi.single i (1:ℤ) : Fin r→ℤ)) :
    0 < integerPairing A k.val l.val := by
  have hfull := dominant_positive_root_full_support A hd hs hp ho l hl hldom
  obtain ⟨i,hi,hpi⟩ := exists_positive_coordinate_pairing (integerPairing A) k.val hk
    (by rw [k.property];decide)
  have hterm : 0<l.val i*integerPairing A k.val (Pi.single i (1:ℤ) : Fin r→ℤ) :=
    mul_pos (hfull i) hpi
  have hsum : integerPairing A k.val l.val=
      ∑j,l.val j*integerPairing A k.val (Pi.single j (1:ℤ) : Fin r→ℤ) := by
    rw [integer_symmetric A hs k.val l.val,pairing_coordinate_sum_left]
    apply Finset.sum_congr rfl
    intro j hj
    rw [integer_symmetric A hs (Pi.single j (1:ℤ) : Fin r→ℤ) k.val]
  rw [hsum]
  exact lt_of_lt_of_le hterm (Finset.single_le_sum
    (fun j _=>mul_nonneg (hl j) (hkdom j)) (Finset.mem_univ i))

theorem dominant_positive_root_unique (k l : Roots A) (hk : ∀i,0≤k.val i)
    (hl : ∀i,0≤l.val i)
    (hkdom : ∀i,0 ≤ integerPairing A k.val (Pi.single i (1:ℤ) : Fin r→ℤ))
    (hldom : ∀i,0 ≤ integerPairing A l.val (Pi.single i (1:ℤ) : Fin r→ℤ)) : k=l := by
  by_contra hne
  have hpos := dominant_positive_pair_pos A hd hs hp ho k l hk hl hkdom hldom
  have hb := root_pairing_bounds A hs hp k l
  have htwo : integerPairing A k.val l.val≠2 := by
    intro he
    exact hne ((root_pairing_eq_two_iff A hs hp k l).mp he)
  have hpair : integerPairing A k.val l.val=1 := by omega
  have hnorm : integerPairing A (k.val-l.val) (k.val-l.val)=2 := by
    rw [norm_sub A hs,k.property,l.property,hpair]
    norm_num
  have hev : ∀i,Even (A i i) := by intro i;rw [hd i];decide
  rcases norm_two_coordinates_one_sign A hs hp hev ho (k.val-l.val) hnorm with hplus|hminus
  · have hnonneg := dominant_pair_nonneg A hs l.val (k.val-l.val) hldom hplus
    have he : integerPairing A l.val (k.val-l.val)= -1 := by
      rw [map_sub,integer_symmetric A hs l.val k.val,hpair,l.property]
      norm_num
    rw [he] at hnonneg
    omega
  · have hplus : ∀i,0≤(l.val-k.val) i := by
      intro i
      have hi := hminus i
      change k.val i-l.val i≤0 at hi
      change 0≤l.val i-k.val i
      omega
    have hnonneg := dominant_pair_nonneg A hs k.val (l.val-k.val) hkdom hplus
    have he : integerPairing A k.val (l.val-k.val)= -1 := by
      rw [map_sub,hpair,k.property]
      norm_num
    rw [he] at hnonneg
    omega

end SymmetricSubgroupAsymptotics.CFSGNormTwoCoordinateDominantRootUnique
