import SymmetricSubgroupAsymptotics.CFSGNormTwoCoordinateOriginalLeadingHom
import SymmetricSubgroupAsymptotics.CFSGNormTwoCoordinateSimpleLeadingImages

/-! In the ORIGINAL positive group, a positive root piece has nonzero
abelianized image exactly when its lattice root is simple. Its full
image is then the corresponding literal coordinate axis. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGNormTwoCoordinateOriginalSimpleLeadingImages
open CFSG.Models.Chevalley CFSGIntegerMatrixPairing CFSGNormTwoRootPairing
open CFSGGeckSerreRepresentation CFSGNormTwoCoordinateOriginalPositiveCenter
open CFSGNormTwoCoordinateOriginalAllRootLines CFSGNormTwoCoordinateOriginalLeadingHom
open CFSGNormTwoCoordinateSimpleLeadingImages CFSGSimpleCoordinateAxes
variable {r : ℕ} (A : Matrix (Fin r) (Fin r) ℤ) (hd : ∀i,A i i=2)
    (hs : A.transpose=A) (hp : (rationalMatrix A).PosDef)
    (ho : ∀i j,i≠j→A i j≤0)
    [Fintype (Roots A)] [DecidableEq (Roots A)]
    [(rootPairing A hs hp).IsReduced] [(rootPairing A hs hp).IsIrreducible]
    (K : Type) [Field K] [Finite K] [Nontrivial (Fin r)]
local notation "b₀" => coordinateBase A hd hs hp ho
local notation "s₀" => coordinateIndexEquiv A hd hs hp ho

theorem original_simple_leading_image (p : ℕ) [Fact p.Prime] [CharP K p]
    [IsSimpleGroup (Projective (cartan b₀ s₀) K)] (i j : Fin r) :
    ((originalFullRootLine A hd hs hp ho K i (s₀ j)).subgroupOf
      (originalPositive A hd hs hp ho K i)).map (originalLeadingHom A hd hs hp ho K p i)=
        axis (K:=K) j := by
  have hj : ∀t,0≤(s₀ j : Roots A).val t := by
    intro t
    change 0≤(Pi.single j (1:ℤ) : Fin r→ℤ) t
    simp only [Pi.single_apply]
    split_ifs <;> norm_num
  rw [original_root_leading_image A hd hs hp ho K p i (s₀ j) hj]
  exact simple_root_leading_image A hd hs hp ho K j

theorem original_nonsimple_leading_image (p : ℕ) [Fact p.Prime] [CharP K p]
    [IsSimpleGroup (Projective (cartan b₀ s₀) K)] (i : Fin r) (k : Roots A)
    (hk : ∀j,0≤k.val j) (hns : ∀j : Fin r,k≠(s₀ j : Roots A)) :
    ((originalFullRootLine A hd hs hp ho K i k).subgroupOf
      (originalPositive A hd hs hp ho K i)).map (originalLeadingHom A hd hs hp ho K p i)=⊥ := by
  rw [original_root_leading_image A hd hs hp ho K p i k hk]
  exact nonsimple_root_leading_image A hd hs hp ho K k hns

theorem original_simple_piece_not_le_derived (p : ℕ) [Fact p.Prime] [CharP K p]
    [IsSimpleGroup (Projective (cartan b₀ s₀) K)] (i j : Fin r) :
    ¬(originalFullRootLine A hd hs hp ho K i (s₀ j)).subgroupOf
      (originalPositive A hd hs hp ho K i)≤commutator (originalPositive A hd hs hp ho K i) := by
  intro h
  have hc : Multiplicative.ofAdd (Pi.single j (1:K) : Fin r→K)∈
      ((originalFullRootLine A hd hs hp ho K i (s₀ j)).subgroupOf
        (originalPositive A hd hs hp ho K i)).map (originalLeadingHom A hd hs hp ho K p i) := by
    rw [original_simple_leading_image A hd hs hp ho K p i j]
    exact single_mem_axis j 1
  obtain ⟨u,hu,he⟩ := hc
  have hku : u∈(originalLeadingHom A hd hs hp ho K p i).ker := by
    rw [originalLeadingHom_kernel A hd hs hp ho K p i]
    exact h hu
  have hz : originalLeadingHom A hd hs hp ho K p i u=1 := hku
  have hh := congrArg (fun c : Multiplicative (Fin r→K)=>c.toAdd j) (he.symm.trans hz)
  exact (one_ne_zero : (1:K)≠0) (by simpa [Pi.single_apply] using hh)

theorem original_root_piece_visible_iff_simple (p : ℕ) [Fact p.Prime] [CharP K p]
    [IsSimpleGroup (Projective (cartan b₀ s₀) K)] (i : Fin r) (k : Roots A)
    (hk : ∀j,0≤k.val j) :
    (¬(originalFullRootLine A hd hs hp ho K i k).subgroupOf (originalPositive A hd hs hp ho K i)≤
      commutator (originalPositive A hd hs hp ho K i))↔∃j : Fin r,k=(s₀ j : Roots A) := by
  classical
  constructor
  · intro h
    by_contra hn
    apply h
    exact original_nonsimple_root_piece_le_derived A hd hs hp ho K p i k hk
      (fun j hj=>hn ⟨j,hj⟩)
  · rintro ⟨j,rfl⟩
    exact original_simple_piece_not_le_derived A hd hs hp ho K p i j

end SymmetricSubgroupAsymptotics.CFSGNormTwoCoordinateOriginalSimpleLeadingImages
