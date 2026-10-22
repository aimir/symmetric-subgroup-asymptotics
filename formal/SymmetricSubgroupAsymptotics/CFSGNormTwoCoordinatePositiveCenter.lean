import SymmetricSubgroupAsymptotics.CFSGFiniteFilteredCenter
import SymmetricSubgroupAsymptotics.CFSGNormTwoCoordinateCentralHeightFactor
import SymmetricSubgroupAsymptotics.CFSGNormTwoCoordinatePositiveHeightNormalForm

/-! The FULL centre of the literal Geck MATRIX image-U is exactly its
dominant positive root subgroup, uniformly in characteristic. The
finite-height descent uses actual root factorization and unit brackets.
Original Serre/projective Sylow transfer is not asserted by this file. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGNormTwoCoordinatePositiveCenter
open CFSGIntegerMatrixPairing CFSGNormTwoRootPairing
open CFSGNormTwoCoordinateRootHeightFiltration CFSGNormTwoCoordinateRootHeightQuotient
open CFSGNormTwoCoordinateRootHeightBound CFSGNormTwoCoordinatePositiveHeightNormalForm
open CFSGNormTwoCoordinateRootSubgroup CFSGNormTwoCoordinateHighestRoot
open CFSGNormTwoCoordinateHighestRootCentral CFSGNormTwoCoordinateCentralHeightFactor
open CFSGFiniteFilteredCenter
variable {r : ℕ} (A : Matrix (Fin r) (Fin r) ℤ) (hd : ∀i,A i i=2)
    (hs : A.transpose=A) (hp : (rationalMatrix A).PosDef)
    (ho : ∀i j,i≠j→A i j≤0)
    [Fintype (Roots A)] [DecidableEq (Roots A)]
    [(rootPairing A hs hp).IsReduced] [(rootPairing A hs hp).IsIrreducible]
local notation "s₀" => coordinateIndexEquiv A hd hs hp ho

theorem center_eq_dominant_root_subgroup (K : Type) [Field K] (θ : Roots A)
    (hθ : ∀i,0≤θ.val i)
    (hdom : ∀i,0 ≤ integerPairing A θ.val (Pi.single i (1:ℤ) : Fin r→ℤ)) :
    Subgroup.center (PositiveGroup A hd hs hp ho K)=
      (rootSubgroup A hd hs hp ho K θ).subgroupOf (PositiveGroup A hd hs hp ho K) := by
  apply le_antisymm
  · let N : ℕ→Subgroup (PositiveGroup A hd hs hp ho K) :=
      fun n=>heightTailInPositive A hd hs hp ho K ((n:ℤ)+1)
    let T := (rootSubgroup A hd hs hp ho K θ).subgroupOf (PositiveGroup A hd hs hp ho K)
    have hfirst : N 0=⊤ := by
      change (heightTail A hd hs hp ho K 1).subgroupOf (PositiveGroup A hd hs hp ho K)=⊤
      rw [heightTail_one_eq_positive,Subgroup.subgroupOf_self]
    have hlast : N (rootHeightBound A)=⊥ := by
      change (heightTail A hd hs hp ho K ((rootHeightBound A:ℤ)+1)).subgroupOf
        (PositiveGroup A hd hs hp ho K)=⊥
      rw [final_heightTail_eq_bot,Subgroup.bot_subgroupOf]
    apply center_le_of_filtered_steps N T (rootHeightBound A) hfirst hlast
    intro n hn x hx hz
    have he := central_height_factor A hd hs hp ho K θ hθ hdom ((n:ℤ)+1)
      (by omega) x hx hz
    have hcast : (((n+1:ℕ):ℤ)+1)=(n:ℤ)+1+1 := by omega
    simpa only [N,T,hcast] using he
  · exact dominant_root_subgroup_le_center A hd hs hp ho K θ hθ hdom

theorem exists_root_subgroup_center (K : Type) [Field K] [Nonempty (Fin r)] :
    ∃θ : Roots A,(∀i,0≤θ.val i) ∧
      (∀i,0 ≤ integerPairing A θ.val (Pi.single i (1:ℤ) : Fin r→ℤ)) ∧
      Subgroup.center (PositiveGroup A hd hs hp ho K)=
        (rootSubgroup A hd hs hp ho K θ).subgroupOf (PositiveGroup A hd hs hp ho K) := by
  classical
  let i : Fin r := Classical.arbitrary _
  have hi : ∀j,0≤(s₀ i : Roots A).val j := by
    intro j
    change 0≤(Pi.single i (1:ℤ) : Fin r→ℤ) j
    simp only [Pi.single_apply]
    split_ifs <;> norm_num
  obtain ⟨θ,hθ,hdom⟩ := exists_dominant_positive_root A hd hs hp ho (s₀ i) hi
  exact ⟨θ,hθ,hdom,center_eq_dominant_root_subgroup A hd hs hp ho K θ hθ hdom⟩

end SymmetricSubgroupAsymptotics.CFSGNormTwoCoordinatePositiveCenter
