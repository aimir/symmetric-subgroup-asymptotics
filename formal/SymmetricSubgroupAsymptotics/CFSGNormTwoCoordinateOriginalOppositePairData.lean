import SymmetricSubgroupAsymptotics.CFSGNormTwoCoordinateOriginalOppositeAlignment
import SymmetricSubgroupAsymptotics.CFSGNormTwoCoordinateOriginalOrderLower

/-! The two literal original projective root-generated subgroups have
trivial intersection and equal size. Central-kernel separation of ALL
p-elements, not separate restriction injectivity, proves disjointness. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGNormTwoCoordinateOriginalOppositePairData
open CFSG.Models.Chevalley CFSGIntegerMatrixPairing CFSGNormTwoRootPairing
open CFSGGeckSerreRepresentation CFSGNormTwoGeckIntegralRealization
open CFSGNormTwoCoordinateOriginalProjection CFSGNormTwoCoordinateOriginalCentralKernel
open CFSGNormTwoCoordinateElementaryRootParameters CFSGNormTwoCoordinatePositiveSylow
open CFSGNormTwoGeckWeylWordDegree CFSGNormTwoGeckWeylLatticeLinear
open CFSGNormTwoGeckPositivePGroup CFSGNormTwoCoordinatePositivePGroup
open CFSGNormTwoGeckOppositeIntersection CFSGNormTwoCoordinateHeight
open CFSGNormTwoCoordinatePositiveQuotientInjectivity
open CFSGNormTwoCoordinateOriginalPositiveCenter CFSGNormTwoCoordinateOriginalOppositeAlignment
variable {r : ℕ} (A : Matrix (Fin r) (Fin r) ℤ) (hd : ∀j,A j j=2)
    (hs : A.transpose=A) (hp : (rationalMatrix A).PosDef)
    (ho : ∀i j,i≠j→A i j≤0)
    [Fintype (Roots A)] [DecidableEq (Roots A)]
    [(rootPairing A hs hp).IsReduced] [(rootPairing A hs hp).IsIrreducible]
    (K : Type) [Field K] [Finite K] [Nontrivial (Fin r)]
local notation "b₀" => coordinateBase A hd hs hp ho
local notation "s₀" => coordinateIndexEquiv A hd hs hp ho

theorem original_opposite_disjoint_and_card
    (ε : Fin r→ℤ) (hε : ∀j,ε j*ε j=1) (hA : ∀i j,ε i*|A i j|=A j i*ε j)
    (hidentity : ∀w : List (Fin r),wordUnit A hs hp b₀ s₀ K w∈
      Subgroup.normalizer (rootGroup A hs hp b₀ s₀ K false : Set _)→wordLinear A hs hp b₀ s₀ w=1)
    (p : ℕ) [Fact p.Prime] [CharP K p]
    [IsSimpleGroup (Projective (cartan b₀ s₀) K)] (i : Fin r) :
    originalPositive A hd hs hp ho K i⊓originalNegative A hd hs hp ho K i=⊥ ∧
      Nat.card (originalNegative A hd hs hp ho K i)=Nat.card (originalPositive A hd hs hp ho K i) := by
  let H := ElementaryGroup A hd hs hp ho K
  let U := rootGroup A hs hp b₀ s₀ K false
  let V := rootGroup A hs hp b₀ s₀ K true
  have hjoin : U⊔V=H := positive_sup_negative A hs hp b₀ s₀ K
  have hUH : U≤H := by rw [←hjoin]; exact le_sup_left
  have hVH : V≤H := by rw [←hjoin]; exact le_sup_right
  let UH := U.subgroupOf H
  let VH := V.subgroupOf H
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
  have hUp : IsPGroup p UH :=
    (rootGroup_isPGroup A hd hs hp ho s₀ K p false).of_injective
      (Subgroup.subgroupOfEquivOfLe hUH).toMonoidHom (Subgroup.subgroupOfEquivOfLe hUH).injective
  have hVp : IsPGroup p VH :=
    (rootGroup_isPGroup A hd hs hp ho s₀ K p true).of_injective
      (Subgroup.subgroupOfEquivOfLe hVH).toMonoidHom (Subgroup.subgroupOfEquivOfLe hVH).injective
  have hUV : UH⊓VH=⊥ := by
    apply le_antisymm _ bot_le
    intro x hx
    have hm : x.val∈U⊓V := hx
    rw [positive_inf_negative A hs hp b₀ s₀ coordinateHeight
      (simple_height A hd hs hp ho) K,Subgroup.mem_bot] at hm
    exact Subgroup.mem_bot.mpr (Subtype.ext hm)
  constructor
  · rw [originalPositive_eq_map A hd hs hp ho K i]
    exact CFSGCentralKernelPElements.disjoint_map f P hP hker UH VH hUp hVp hUV
  · have hc := Nat.card_congr ((MulAut.conj
        (CFSGNormTwoGeckFieldOpposition.oppositionUnit A hs hp b₀ K)).subgroupMap U).toEquiv
    change Nat.card U=Nat.card (U.map
      (MulAut.conj (CFSGNormTwoGeckFieldOpposition.oppositionUnit A hs hp b₀ K)).toMonoidHom) at hc
    rw [opposition_positive_eq_negative A hs hp b₀ s₀ K] at hc
    calc
      Nat.card (originalNegative A hd hs hp ho K i)=Nat.card VH :=
        CFSGCentralKernelPElements.p_subgroup_card_map f P hP hker VH hVp
      _=Nat.card V := Nat.card_congr (Subgroup.subgroupOfEquivOfLe hVH).toEquiv
      _=Nat.card U := hc.symm
      _=Nat.card (originalPositive A hd hs hp ho K i) :=
        Nat.card_congr (originalPositiveEquiv A hd hs hp ho K p i).toEquiv

end SymmetricSubgroupAsymptotics.CFSGNormTwoCoordinateOriginalOppositePairData
