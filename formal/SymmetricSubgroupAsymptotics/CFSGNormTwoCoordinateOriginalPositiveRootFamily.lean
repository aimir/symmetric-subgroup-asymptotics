import SymmetricSubgroupAsymptotics.CFSGNormTwoCoordinateOriginalRootContainment
import SymmetricSubgroupAsymptotics.CFSGNormTwoCoordinateRootFamilyBruhatCover
import SymmetricSubgroupAsymptotics.CFSGNormTwoCoordinateOriginalRootFamily
import SymmetricSubgroupAsymptotics.CFSGSubgroupConjugateRestriction
import Mathlib.Tactic.Group

/-! The intrinsic dominant-root conjugacy family INSIDE the original
positive Sylow consists of its positive-lattice-root conjugates under
that SAME positive group. This is a quotient transport of an actual
Bruhat cover, not a lift of an arbitrary projective automorphism. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGNormTwoCoordinateOriginalPositiveRootFamily
open CFSG.Models.Chevalley CFSGIntegerMatrixPairing CFSGNormTwoRootPairing
open CFSGGeckSerreRepresentation CFSGNormTwoCoordinateRootSubgroup
open CFSGNormTwoCoordinateElementaryRootParameters CFSGNormTwoCoordinateRootHeightQuotient
open CFSGNormTwoCoordinateOriginalProjection CFSGNormTwoCoordinateOriginalPositiveCenter
open CFSGNormTwoCoordinatePositiveQuotientInjectivity CFSGNormTwoCoordinateOriginalRootFamily
open CFSGNormTwoCoordinateOriginalAllRootLines CFSGNormTwoCoordinateOriginalRootContainment
open CFSGNormTwoCoordinateRootFamilyBruhatCover CFSGSubgroupConjugateRestriction
open CFSGNormTwoGeckPositivePGroup CFSGNormTwoGeckWeylWordDegree CFSGNormTwoGeckWeylLatticeLinear
variable {r : ℕ} (A : Matrix (Fin r) (Fin r) ℤ) (hd : ∀i,A i i=2)
    (hs : A.transpose=A) (hp : (rationalMatrix A).PosDef)
    (ho : ∀i j,i≠j→A i j≤0)
    [Fintype (Roots A)] [DecidableEq (Roots A)]
    [(rootPairing A hs hp).IsReduced] [(rootPairing A hs hp).IsIrreducible]
    (K : Type) [Field K]
local notation "b₀" => coordinateBase A hd hs hp ho
local notation "s₀" => coordinateIndexEquiv A hd hs hp ho

theorem original_root_conjugate_eq_positive_conjugate
    [IsSimpleGroup (Projective (cartan b₀ s₀) K)] (i : Fin r) (θ : Roots A)
    (hθ : ∀j,0≤θ.val j)
    (hdom : ∀j,0 ≤ integerPairing A θ.val (Pi.single j (1:ℤ) : Fin r→ℤ))
    (g : Projective (cartan b₀ s₀) K) :
    ∃k : Roots A,∃u : originalPositive A hd hs hp ho K i,
      originalConjugateRootLine A hd hs hp ho K i θ g=
        (originalFullRootLine A hd hs hp ho K i k).map (MulAut.conj u.val).toMonoidHom := by
  let H := ElementaryGroup A hd hs hp ho K
  let f := originalProjection A hd hs hp ho K i
  obtain ⟨h,hh⟩ : ∃h : H,f h=g := originalProjection_surjective A hd hs hp ho K i g
  obtain ⟨k,u,hm⟩ := root_conjugate_eq_positive_conjugate A hd hs hp ho K θ hθ hdom h
  let uH : H := positiveInclusion A hd hs hp ho K u
  let Rθ := elementaryRootSubgroup A hd hs hp ho K θ
  let Rk := elementaryRootSubgroup A hd hs hp ho K k
  have hRθ : Rθ.map H.subtype=rootSubgroup A hd hs hp ho K θ :=
    Subgroup.map_subgroupOf_eq_of_le (rootSubgroup_le_elementary A hd hs hp ho K θ)
  have hRk : Rk.map H.subtype=rootSubgroup A hd hs hp ho K k :=
    Subgroup.map_subgroupOf_eq_of_le (rootSubgroup_le_elementary A hd hs hp ho K k)
  have hH : Rθ.map (MulAut.conj h).toMonoidHom=Rk.map (MulAut.conj uH).toMonoidHom := by
    apply Subgroup.map_injective H.subtype_injective
    rw [map_conjugate,map_conjugate,hRθ,hRk]
    exact hm
  have hpush := congrArg (fun S : Subgroup H=>S.map f) hH
  dsimp only at hpush
  rw [map_conjugate,map_conjugate] at hpush
  change (originalFullRootLine A hd hs hp ho K i θ).map (MulAut.conj (f h)).toMonoidHom=
    (originalFullRootLine A hd hs hp ho K i k).map (MulAut.conj (f uH)).toMonoidHom at hpush
  rw [originalFullRootLine_eq_positive A hd hs hp ho K i θ hθ,hh] at hpush
  exact ⟨k,⟨f uH,⟨u,rfl⟩⟩,hpush⟩

theorem contained_original_root_family_positive [Finite K] [Nontrivial (Fin r)]
    (ε : Fin r→ℤ) (hε : ∀j,ε j*ε j=1) (hA : ∀i j,ε i*|A i j|=A j i*ε j)
    (hidentity : ∀w : List (Fin r),wordUnit A hs hp b₀ s₀ K w∈
      Subgroup.normalizer (rootGroup A hs hp b₀ s₀ K false : Set _)→
        wordLinear A hs hp b₀ s₀ w=1)
    (p : ℕ) [Fact p.Prime] [CharP K p]
    [IsSimpleGroup (Projective (cartan b₀ s₀) K)] (i : Fin r) (θ : Roots A)
    (hθ : ∀j,0≤θ.val j)
    (hdom : ∀j,0 ≤ integerPairing A θ.val (Pi.single j (1:ℤ) : Fin r→ℤ))
    (g : Projective (cartan b₀ s₀) K)
    (hg : originalConjugateRootLine A hd hs hp ho K i θ g≤originalPositive A hd hs hp ho K i) :
    ∃k : Roots A,(∀j,0≤k.val j) ∧ ∃u : originalPositive A hd hs hp ho K i,
      originalConjugateRootLine A hd hs hp ho K i θ g=
        (originalFullRootLine A hd hs hp ho K i k).map (MulAut.conj u.val).toMonoidHom := by
  obtain ⟨k,u,he⟩ := original_root_conjugate_eq_positive_conjugate A hd hs hp ho K i θ hθ hdom g
  have hkU : originalFullRootLine A hd hs hp ho K i k≤originalPositive A hd hs hp ho K i := by
    intro x hx
    have hconj : u.val*x*u.val⁻¹∈originalPositive A hd hs hp ho K i := by
      apply hg
      rw [he]
      exact ⟨x,hx,rfl⟩
    have hxU := (originalPositive A hd hs hp ho K i).mul_mem
      ((originalPositive A hd hs hp ho K i).mul_mem
        ((originalPositive A hd hs hp ho K i).inv_mem u.property) hconj) u.property
    convert hxU using 1 <;> group
  have hk := (originalFullRootLine_le_positive_iff A hd hs hp ho K ε hε hA hidentity p i k).mp hkU
  exact ⟨k,hk,u,he⟩

end SymmetricSubgroupAsymptotics.CFSGNormTwoCoordinateOriginalPositiveRootFamily
