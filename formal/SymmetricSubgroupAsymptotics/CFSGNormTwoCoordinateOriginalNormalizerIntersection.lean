import SymmetricSubgroupAsymptotics.CFSGNormTwoCoordinateElementaryNormalizerIntersection
import SymmetricSubgroupAsymptotics.CFSGNormTwoCoordinateOriginalOppositePairData
import SymmetricSubgroupAsymptotics.CFSGQuotientNormalizerIntersection
import SymmetricSubgroupAsymptotics.CFSGNormTwoCoordinateCanonicalSimpleRootLine

/-! Full-normalizer simple-root recovery in the ORIGINAL projective
model. The quotient intersection is justified by the actual central
kernel; full normalizer equality uses proved p-element separation. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGNormTwoCoordinateOriginalNormalizerIntersection
open CFSG.Models.Chevalley CFSGIntegerMatrixPairing CFSGNormTwoRootPairing
open CFSGGeckSerreRepresentation CFSGNormTwoGeckIntegralRealization
open CFSGNormTwoCoordinateOriginalProjection CFSGNormTwoCoordinateOriginalCentralKernel
open CFSGNormTwoCoordinateElementaryRootParameters CFSGNormTwoCoordinatePositiveSylow
open CFSGNormTwoGeckWeylWordDegree CFSGNormTwoGeckWeylLatticeLinear
open CFSGNormTwoGeckPositivePGroup CFSGNormTwoCoordinatePositivePGroup CFSGSerreQuadraticMatrix
open CFSGNormTwoCoordinatePositiveQuotientInjectivity
open CFSGNormTwoCoordinateOriginalPositiveCenter CFSGNormTwoCoordinateOriginalOppositeAlignment
open CFSGNormTwoCoordinateElementaryNormalizerIntersection CFSGQuotientNormalizerIntersection
variable {r : ℕ} (A : Matrix (Fin r) (Fin r) ℤ) (hd : ∀j,A j j=2)
    (hs : A.transpose=A) (hp : (rationalMatrix A).PosDef)
    (ho : ∀i j,i≠j→A i j≤0)
    [Fintype (Roots A)] [DecidableEq (Roots A)]
    [(rootPairing A hs hp).IsReduced] [(rootPairing A hs hp).IsIrreducible]
    (K : Type) [Field K]
local notation "b₀" => coordinateBase A hd hs hp ho
local notation "s₀" => coordinateIndexEquiv A hd hs hp ho
local notation "D" => realizationData A hs hp b₀ s₀

def originalSimpleRootGroup [IsSimpleGroup (Projective (cartan b₀ s₀) K)]
    (i j : Fin r) : Subgroup (Projective (cartan b₀ s₀) K) :=
  ((canonicalRootSubgroup D K false j).subgroupOf (ElementaryGroup A hd hs hp ho K)).map
    (originalProjection A hd hs hp ho K i)

def originalWeylRootGroup [IsSimpleGroup (Projective (cartan b₀ s₀) K)]
    (i j : Fin r) : Subgroup (Projective (cartan b₀ s₀) K) :=
  ((Subgroup.closure {canonicalWeyl D K j}).subgroupOf (ElementaryGroup A hd hs hp ho K)).map
    (originalProjection A hd hs hp ho K i)

theorem originalSimpleRootGroup_eq_fullRootLine
    [IsSimpleGroup (Projective (cartan b₀ s₀) K)] (i j : Fin r) :
    originalSimpleRootGroup A hd hs hp ho K i j=
      CFSGNormTwoCoordinateOriginalAllRootLines.originalFullRootLine A hd hs hp ho K i (s₀ j) :=
  CFSGNormTwoCoordinateCanonicalSimpleRootLine.original_canonical_simple_root_line A hd hs hp ho K i j

theorem originalProjection_normalizer_map [Finite K] [Nontrivial (Fin r)]
    (ε : Fin r→ℤ) (hε : ∀j,ε j*ε j=1) (hA : ∀i j,ε i*|A i j|=A j i*ε j)
    (hidentity : ∀w : List (Fin r),wordUnit A hs hp b₀ s₀ K w∈
      Subgroup.normalizer (rootGroup A hs hp b₀ s₀ K false : Set _)→wordLinear A hs hp b₀ s₀ w=1)
    (p : ℕ) [Fact p.Prime] [CharP K p]
    [IsSimpleGroup (Projective (cartan b₀ s₀) K)] (i : Fin r)
    (R : Subgroup (ElementaryGroup A hd hs hp ho K)) (hR : IsPGroup p R) :
    (Subgroup.normalizer (R : Set _)).map (originalProjection A hd hs hp ho K i)=
      Subgroup.normalizer (R.map (originalProjection A hd hs hp ho K i) : Set _) := by
  let H := ElementaryGroup A hd hs hp ho K
  let f := originalProjection A hd hs hp ho K i
  let P := canonicalPositiveSylow A hd hs hp ho K ε hε hA hidentity p
  have hP : Function.Injective (f.comp (P : Subgroup H).subtype) := by
    intro x y he
    have hh := originalProjection_positive_injective A hd hs hp ho K p i
      (a₁ := ⟨x.val.val,x.property⟩) (a₂ := ⟨y.val.val,y.property⟩) he
    have hval : x.val.val=y.val.val :=
      congrArg (fun z : CFSGNormTwoCoordinateRootHeightQuotient.PositiveGroup A hd hs hp ho K=>z.val) hh
    exact Subtype.ext (Subtype.ext hval)
  exact normalizer_map_eq_of_central_p_separation f (originalProjection_surjective A hd hs hp ho K i)
    P hP (originalProjection_kernel_eq_center A hd hs hp ho K i).le R hR

theorem original_negative_weyl_join_eq_root_join [Finite K] [Nontrivial (Fin r)]
    (ε : Fin r→ℤ) (hε : ∀j,ε j*ε j=1) (hA : ∀i j,ε i*|A i j|=A j i*ε j)
    (hidentity : ∀w : List (Fin r),wordUnit A hs hp b₀ s₀ K w∈
      Subgroup.normalizer (rootGroup A hs hp b₀ s₀ K false : Set _)→wordLinear A hs hp b₀ s₀ w=1)
    (p : ℕ) [Fact p.Prime] [CharP K p]
    [IsSimpleGroup (Projective (cartan b₀ s₀) K)] (i j : Fin r) :
    Subgroup.normalizer (originalNegative A hd hs hp ho K i : Set _)⊔
      originalWeylRootGroup A hd hs hp ho K i j=
    Subgroup.normalizer (originalNegative A hd hs hp ho K i : Set _)⊔
      originalSimpleRootGroup A hd hs hp ho K i j := by
  let H := ElementaryGroup A hd hs hp ho K
  let U := rootGroup A hs hp b₀ s₀ K false
  let V := rootGroup A hs hp b₀ s₀ K true
  have hjoin : U⊔V=H := positive_sup_negative A hs hp b₀ s₀ K
  have hVH : V≤H := by rw [←hjoin]; exact le_sup_right
  have hVp : IsPGroup p (V.subgroupOf H) :=
    (rootGroup_isPGroup A hd hs hp ho s₀ K p true).of_injective
      (Subgroup.subgroupOfEquivOfLe hVH).toMonoidHom (Subgroup.subgroupOfEquivOfLe hVH).injective
  have hh := congrArg (fun S=>S.map (originalProjection A hd hs hp ho K i))
    (elementary_negative_weyl_join_eq_root_join A hd hs hp ho K j)
  dsimp only at hh
  rw [Subgroup.map_sup,Subgroup.map_sup,
    originalProjection_normalizer_map A hd hs hp ho K ε hε hA hidentity p i _ hVp] at hh
  exact hh

theorem original_opposite_normalizer_intersection [Finite K] [Nontrivial (Fin r)]
    (ε : Fin r→ℤ) (hε : ∀j,ε j*ε j=1) (hA : ∀i j,ε i*|A i j|=A j i*ε j)
    (hidentity : ∀w : List (Fin r),wordUnit A hs hp b₀ s₀ K w∈
      Subgroup.normalizer (rootGroup A hs hp b₀ s₀ K false : Set _)→wordLinear A hs hp b₀ s₀ w=1)
    (p : ℕ) [Fact p.Prime] [CharP K p]
    [IsSimpleGroup (Projective (cartan b₀ s₀) K)] (i j : Fin r) :
    originalPositive A hd hs hp ho K i ⊓
      (Subgroup.normalizer (originalNegative A hd hs hp ho K i : Set _)⊔
        originalSimpleRootGroup A hd hs hp ho K i j)=
      originalSimpleRootGroup A hd hs hp ho K i j := by
  let H := ElementaryGroup A hd hs hp ho K
  let U := rootGroup A hs hp b₀ s₀ K false
  let V := rootGroup A hs hp b₀ s₀ K true
  let UH := U.subgroupOf H
  let VH := V.subgroupOf H
  let R := (canonicalRootSubgroup D K false j).subgroupOf H
  have hjoin : U⊔V=H := positive_sup_negative A hs hp b₀ s₀ K
  have hVH : V≤H := by rw [←hjoin]; exact le_sup_right
  let f := originalProjection A hd hs hp ho K i
  let P := canonicalPositiveSylow A hd hs hp ho K ε hε hA hidentity p
  have hP : Function.Injective (f.comp (P : Subgroup H).subtype) := by
    intro x y he
    have hh := originalProjection_positive_injective A hd hs hp ho K p i
      (a₁ := ⟨x.val.val,x.property⟩) (a₂ := ⟨y.val.val,y.property⟩) he
    have hval : x.val.val=y.val.val :=
      congrArg (fun z : CFSGNormTwoCoordinateRootHeightQuotient.PositiveGroup A hd hs hp ho K=>z.val) hh
    exact Subtype.ext (Subtype.ext hval)
  have hker : f.ker≤Subgroup.center H :=
    (originalProjection_kernel_eq_center A hd hs hp ho K i).le
  have hVp : IsPGroup p VH :=
    (rootGroup_isPGroup A hd hs hp ho s₀ K p true).of_injective
      (Subgroup.subgroupOfEquivOfLe hVH).toMonoidHom (Subgroup.subgroupOfEquivOfLe hVH).injective
  rw [originalPositive_eq_map A hd hs hp ho K i]
  exact opposite_normalizer_intersection_map f (originalProjection_surjective A hd hs hp ho K i)
    P hP hker UH VH R hVp
      (elementary_opposite_normalizer_intersection A hd hs hp ho K ε hε hA hidentity j)

end SymmetricSubgroupAsymptotics.CFSGNormTwoCoordinateOriginalNormalizerIntersection
