import SymmetricSubgroupAsymptotics.CFSGNormTwoCoordinateOriginalPositiveRootFamily
import SymmetricSubgroupAsymptotics.CFSGNormTwoCoordinateOriginalSimpleLeadingImages
import SymmetricSubgroupAsymptotics.CFSGNormTwoCoordinateOriginalRootRecognition
import SymmetricSubgroupAsymptotics.CFSGCommutativeConjugateImage

/-! Intrinsic recognition of the literal simple coordinate axes in the
ORIGINAL group's positive abelianization. They are precisely the nonzero
leading images of intrinsic root-family members contained in that
positive group. No automorphism lifting or torus-eigenvalue argument. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGNormTwoCoordinateIntrinsicLeadingAxes
open CFSG.Models.Chevalley CFSGIntegerMatrixPairing CFSGNormTwoRootPairing
open CFSGGeckSerreRepresentation CFSGNormTwoCoordinateOriginalPositiveCenter
open CFSGNormTwoCoordinateOriginalRootFamily CFSGNormTwoCoordinateOriginalAllRootLines
open CFSGNormTwoCoordinateOriginalRootRecognition CFSGNormTwoCoordinateOriginalPositiveRootFamily
open CFSGNormTwoCoordinateOriginalRootContainment CFSGNormTwoCoordinateOriginalLeadingHom
open CFSGNormTwoCoordinateOriginalSimpleLeadingImages CFSGSimpleCoordinateAxes
open CFSGSubgroupConjugateRestriction CFSGCommutativeConjugateImage
open CFSGNormTwoGeckPositivePGroup CFSGNormTwoGeckWeylWordDegree CFSGNormTwoGeckWeylLatticeLinear
variable {r : ℕ} (A : Matrix (Fin r) (Fin r) ℤ) (hd : ∀i,A i i=2)
    (hs : A.transpose=A) (hp : (rationalMatrix A).PosDef)
    (ho : ∀i j,i≠j→A i j≤0)
    [Fintype (Roots A)] [DecidableEq (Roots A)]
    [(rootPairing A hs hp).IsReduced] [(rootPairing A hs hp).IsIrreducible]
    (K : Type) [Field K] [Finite K] [Nontrivial (Fin r)]
local notation "b₀" => coordinateBase A hd hs hp ho
local notation "s₀" => coordinateIndexEquiv A hd hs hp ho

def intrinsicLeadingAxes (p : ℕ) [Fact p.Prime] [CharP K p]
    [IsSimpleGroup (Projective (cartan b₀ s₀) K)] (i : Fin r) (θ : Roots A) :
    Set (Subgroup (Multiplicative (Fin r→K))) :=
  {L | L≠⊥ ∧ ∃g : Projective (cartan b₀ s₀) K,
    originalConjugateRootLine A hd hs hp ho K i θ g≤originalPositive A hd hs hp ho K i ∧
      L=((originalConjugateRootLine A hd hs hp ho K i θ g).subgroupOf
        (originalPositive A hd hs hp ho K i)).map (originalLeadingHom A hd hs hp ho K p i)}

theorem intrinsicLeadingAxes_eq_axes
    (ε : Fin r→ℤ) (hε : ∀j,ε j*ε j=1) (hA : ∀i j,ε i*|A i j|=A j i*ε j)
    (hidentity : ∀w : List (Fin r),wordUnit A hs hp b₀ s₀ K w∈
      Subgroup.normalizer (rootGroup A hs hp b₀ s₀ K false : Set _)→wordLinear A hs hp b₀ s₀ w=1)
    (p : ℕ) [Fact p.Prime] [CharP K p]
    [IsSimpleGroup (Projective (cartan b₀ s₀) K)] (i : Fin r) (θ : Roots A)
    (hθ : ∀j,0≤θ.val j)
    (hdom : ∀j,0 ≤ integerPairing A θ.val (Pi.single j (1:ℤ) : Fin r→ℤ)) :
    intrinsicLeadingAxes A hd hs hp ho K p i θ=Set.range (axis (K:=K) (J:=Fin r)) := by
  classical
  ext L
  constructor
  · rintro ⟨hne,g,hg,hL⟩
    obtain ⟨k,hk,u,he⟩ := contained_original_root_family_positive A hd hs hp ho K
      ε hε hA hidentity p i θ hθ hdom g hg
    have hkU := (originalFullRootLine_le_positive_iff A hd hs hp ho K ε hε hA hidentity p i k).mpr hk
    have hr := restrict_conjugate (originalPositive A hd hs hp ho K i)
      (originalFullRootLine A hd hs hp ho K i k)
      (originalConjugateRootLine A hd hs hp ho K i θ g) hkU hg u he.symm
    have hm := congrArg (fun S : Subgroup (originalPositive A hd hs hp ho K i)=>
      S.map (originalLeadingHom A hd hs hp ho K p i)) hr
    dsimp only at hm
    rw [conjugate_map_eq] at hm
    have hsame : L=((originalFullRootLine A hd hs hp ho K i k).subgroupOf
        (originalPositive A hd hs hp ho K i)).map (originalLeadingHom A hd hs hp ho K p i) :=
      hL.trans hm.symm
    obtain ⟨j,hj⟩ : ∃j : Fin r,k=(s₀ j : Roots A) := by
      by_contra hn
      apply hne
      rw [hsame]
      exact original_nonsimple_leading_image A hd hs hp ho K p i k hk (fun j h=>hn ⟨j,h⟩)
    refine ⟨j,?_⟩
    rw [hj,original_simple_leading_image A hd hs hp ho K p i j] at hsame
    exact hsame.symm
  · rintro ⟨j,rfl⟩
    have hj : ∀t,0≤(s₀ j : Roots A).val t := by
      intro t
      change 0≤(Pi.single j (1:ℤ) : Fin r→ℤ) t
      simp only [Pi.single_apply]
      split_ifs <;> norm_num
    have hjU := (originalFullRootLine_le_positive_iff A hd hs hp ho K ε hε hA hidentity p i (s₀ j)).mpr hj
    obtain ⟨g,hg⟩ := original_rootLine_mem_dominant_family A hd hs hp ho K i θ (s₀ j) hθ
    refine ⟨?_,g,?_,?_⟩
    · intro hbot
      have hh := single_mem_axis (K:=K) j 1
      rw [hbot,Subgroup.mem_bot] at hh
      have hz := congrArg (fun c : Multiplicative (Fin r→K)=>c.toAdd j) hh
      exact (one_ne_zero : (1:K)≠0) (by simpa [Pi.single_apply] using hz)
    · rw [←hg]
      exact hjU
    · rw [←hg]
      exact (original_simple_leading_image A hd hs hp ho K p i j).symm

end SymmetricSubgroupAsymptotics.CFSGNormTwoCoordinateIntrinsicLeadingAxes
