import SymmetricSubgroupAsymptotics.CFSGNormTwoCoordinateRootHeightFiltration
import SymmetricSubgroupAsymptotics.CFSGIntegerPairingPositiveDescent

/-! Actual root commutators increase the SUM of their integer heights
inside the Geck matrix image-U. In particular a positive root acts
trivially on each successive height-tail quotient. No filtered-group
commutator bound is assumed as part of a model interface. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGNormTwoCoordinateRootHeightCommutator
open CFSGIntegerMatrixPairing CFSGNormTwoRootPairing CFSGNormTwoPairingBounds
open CFSGIntegerHeightSign CFSGIntegerPairingPositiveDescent
open CFSGNormTwoCoordinateSelectedRootElement CFSGNormTwoCoordinateSelectedRootAdditive
open CFSGNormTwoCoordinatePositivePairCollecting CFSGNormTwoCoordinateRootHeightFiltration

private theorem commutator_eq_one {G : Type*} [Group G] (x y : G) (hc : Commute x y) :
    x*y*x⁻¹*y⁻¹=1 := by rw [hc.eq];group

variable {r : ℕ} (A : Matrix (Fin r) (Fin r) ℤ) (hd : ∀i,A i i=2)
    (hs : A.transpose=A) (hp : (rationalMatrix A).PosDef)
    (ho : ∀i j,i≠j→A i j≤0)
    [Fintype (Roots A)] [DecidableEq (Roots A)]
    [(rootPairing A hs hp).IsReduced] [(rootPairing A hs hp).IsIrreducible]

omit [Fintype (Roots A)] [DecidableEq (Roots A)]
  [(rootPairing A hs hp).IsReduced] [(rootPairing A hs hp).IsIrreducible] in
theorem positive_root_height_pos (k : Roots A) (hk : ∀i,0≤k.val i) : 0<height k.val := by
  have hn : 0 < integerPairing A k.val k.val := by rw [k.property];decide
  obtain ⟨i,hi,_⟩ := exists_positive_coordinate_pairing (integerPairing A) k.val hk hn
  have hsum : k.val i≤height k.val :=
    Finset.single_le_sum (fun j _=>hk j) (Finset.mem_univ i)
  omega

theorem root_commutator_mem_height_add (K : Type) [Field K] (m n : ℤ) (k l : Roots A)
    (hk : ∀i,0≤k.val i) (hl : ∀i,0≤l.val i)
    (hkheight : m≤height k.val) (hlheight : n≤height l.val) (a b : K) :
    selectedRootElement A hd hs hp ho K k a*selectedRootElement A hd hs hp ho K l b*
      (selectedRootElement A hd hs hp ho K k a)⁻¹*(selectedRootElement A hd hs hp ho K l b)⁻¹∈
        heightTail A hd hs hp ho K (m+n) := by
  by_cases hkl : k=l
  · subst l
    rw [commutator_eq_one _ _ (selectedRootElement_commute A hd hs hp ho K k a b)]
    exact (heightTail A hd hs hp ho K (m+n)).one_mem
  have hopp : k.val≠ -l.val := by
    intro he
    have hz : k.val=0 := by
      funext j
      have hj := congrFun he j
      change k.val j= -(l.val j) at hj
      have := hk j
      have := hl j
      change k.val j=0
      omega
    have hn := k.property
    rw [hz] at hn
    norm_num at hn
  rcases root_pairing_interior A hs hp k l hkl hopp with hneg|hother
  · obtain ⟨ε,_,he⟩ := positive_pair_commutator_sign A hd hs hp ho k l hk hl hneg
    rw [he K a b]
    apply rootElement_mem_heightTail A hd hs hp ho K (m+n) (sumRoot A hs k l hneg)
    · exact fun j=>add_nonneg (hk j) (hl j)
    · change m+n≤height (k.val+l.val)
      rw [height_add]
      omega
  · have hc := CFSGNormTwoCoordinatePositivePairCommute.positive_pair_commute
      A hd hs hp ho K k l hk hl hother a b
    rw [commutator_eq_one _ _ hc]
    exact (heightTail A hd hs hp ho K (m+n)).one_mem

theorem root_commutator_mem_next_height (K : Type) [Field K] (h : ℤ) (k l : Roots A)
    (hk : ∀i,0≤k.val i) (hl : ∀i,0≤l.val i) (hlheight : h≤height l.val) (a b : K) :
    selectedRootElement A hd hs hp ho K k a*selectedRootElement A hd hs hp ho K l b*
      (selectedRootElement A hd hs hp ho K k a)⁻¹*(selectedRootElement A hd hs hp ho K l b)⁻¹∈
        heightTail A hd hs hp ho K (h+1) := by
  have hkheight : 1≤height k.val := by have := positive_root_height_pos A k hk;omega
  have hm := root_commutator_mem_height_add A hd hs hp ho K 1 h k l hk hl hkheight hlheight a b
  simpa only [add_comm] using hm

end SymmetricSubgroupAsymptotics.CFSGNormTwoCoordinateRootHeightCommutator
