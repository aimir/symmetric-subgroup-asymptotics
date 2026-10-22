import SymmetricSubgroupAsymptotics.CFSGNormTwoCoordinateOriginalCentralKernel
import SymmetricSubgroupAsymptotics.CFSGNormTwoCoordinateOriginalRootFamily
import SymmetricSubgroupAsymptotics.CFSGNormTwoCoordinatePositiveSylow
import SymmetricSubgroupAsymptotics.CFSGNormTwoCoordinatePositiveCardinality
import SymmetricSubgroupAsymptotics.CFSGCentralKernelPSubgroups

/-! A genuine order lower bound in the ORIGINAL simple projective model.
Central-kernel p-element separation retains the trivial intersection of
opposite groups. Separate restriction injectivity alone is not used. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGNormTwoCoordinateOriginalOrderLower
open CFSG.Models.Chevalley CFSGIntegerMatrixPairing CFSGNormTwoRootPairing
open CFSGGeckSerreRepresentation CFSGNormTwoGeckIntegralRealization
open CFSGNormTwoCoordinateOriginalProjection CFSGNormTwoCoordinateOriginalCentralKernel
open CFSGNormTwoCoordinateElementaryRootParameters CFSGNormTwoCoordinatePositiveSylow
open CFSGNormTwoGeckWeylWordDegree CFSGNormTwoGeckWeylLatticeLinear
open CFSGNormTwoGeckPositivePGroup CFSGNormTwoCoordinatePositivePGroup
open CFSGNormTwoGeckOppositeIntersection CFSGNormTwoCoordinateHeight
open CFSGNormTwoCoordinateRootHeightQuotient CFSGNormTwoCoordinatePositiveRootGenerators
open CFSGNormTwoCoordinatePositiveCardinality CFSGNormTwoCoordinatePositiveQuotientInjectivity
variable {r : ℕ} (A : Matrix (Fin r) (Fin r) ℤ) (hd : ∀ i, A i i = 2)
    (hs : A.transpose = A) (hp : (rationalMatrix A).PosDef)
    (ho : ∀ i j, i ≠ j → A i j ≤ 0)
    [Fintype (Roots A)] [DecidableEq (Roots A)]
    [(rootPairing A hs hp).IsReduced] [(rootPairing A hs hp).IsIrreducible]
    (K : Type) [Field K] [Finite K] [Nontrivial (Fin r)]
local notation "b₀" => coordinateBase A hd hs hp ho
local notation "s₀" => coordinateIndexEquiv A hd hs hp ho

theorem original_card_lower
    (ε : Fin r → ℤ) (hε : ∀ j, ε j * ε j = 1)
    (hA : ∀ i j, ε i * |A i j| = A j i * ε j)
    (hidentity : ∀ w : List (Fin r), wordUnit A hs hp b₀ s₀ K w ∈
      Subgroup.normalizer (rootGroup A hs hp b₀ s₀ K false : Set _) →
        wordLinear A hs hp b₀ s₀ w = 1)
    (p : ℕ) [Fact p.Prime] [CharP K p]
    [IsSimpleGroup (Projective (cartan b₀ s₀) K)] (i : Fin r) :
    Nat.card K ^ (2 * Nat.card (PositiveRoot A)) ≤ Nat.card (Projective (cartan b₀ s₀) K) := by
  let H := ElementaryGroup A hd hs hp ho K
  let U := rootGroup A hs hp b₀ s₀ K false
  let V := rootGroup A hs hp b₀ s₀ K true
  have hjoin : U ⊔ V = H := positive_sup_negative A hs hp b₀ s₀ K
  have hUH : U ≤ H := by rw [← hjoin]; exact le_sup_left
  have hVH : V ≤ H := by rw [← hjoin]; exact le_sup_right
  let UH := U.subgroupOf H
  let VH := V.subgroupOf H
  let f := originalProjection A hd hs hp ho K i
  let P := canonicalPositiveSylow A hd hs hp ho K ε hε hA hidentity p
  have hP : Function.Injective (f.comp (P : Subgroup H).subtype) := by
    intro x y he
    have hh := originalProjection_positive_injective A hd hs hp ho K p i
      (a₁ := ⟨x.val.val, x.property⟩) (a₂ := ⟨y.val.val, y.property⟩) he
    have hval : x.val.val = y.val.val :=
      congrArg (fun z : PositiveGroup A hd hs hp ho K => z.val) hh
    have hH : x.val = y.val := Subtype.ext hval
    exact Subtype.ext hH
  have hker : f.ker ≤ Subgroup.center H :=
    (originalProjection_kernel_eq_center A hd hs hp ho K i).le
  have hUp : IsPGroup p UH :=
    (rootGroup_isPGroup A hd hs hp ho s₀ K p false).of_injective
      (Subgroup.subgroupOfEquivOfLe hUH).toMonoidHom (Subgroup.subgroupOfEquivOfLe hUH).injective
  have hVp : IsPGroup p VH :=
    (rootGroup_isPGroup A hd hs hp ho s₀ K p true).of_injective
      (Subgroup.subgroupOfEquivOfLe hVH).toMonoidHom (Subgroup.subgroupOfEquivOfLe hVH).injective
  have hUV : UH ⊓ VH = ⊥ := by
    apply le_antisymm _ bot_le
    intro x hx
    have hm : x.val ∈ U ⊓ V := hx
    rw [positive_inf_negative A hs hp b₀ s₀ coordinateHeight
      (simple_height A hd hs hp ho) K, Subgroup.mem_bot] at hm
    exact Subgroup.mem_bot.mpr (Subtype.ext hm)
  letI : Finite (Projective (cartan b₀ s₀) K) :=
    CFSGNormTwoCoordinateOriginalRootFamily.original_projective_finite A hd hs hp ho K i
  have hh := CFSGCentralKernelPElements.disjoint_p_subgroups_card_mul_le f P hP hker
    UH VH hUp hVp hUV
  have hUcard : Nat.card UH = Nat.card K ^ Nat.card (PositiveRoot A) :=
    (Nat.card_congr (Subgroup.subgroupOfEquivOfLe hUH).toEquiv).trans
      (positive_card A hd hs hp ho K)
  have hVcard : Nat.card VH = Nat.card K ^ Nat.card (PositiveRoot A) := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hVH).toEquiv]
    have hc := Nat.card_congr ((MulAut.conj
      (CFSGNormTwoGeckFieldOpposition.oppositionUnit A hs hp b₀ K)).subgroupMap U).toEquiv
    change Nat.card U = Nat.card (U.map
      (MulAut.conj (CFSGNormTwoGeckFieldOpposition.oppositionUnit A hs hp b₀ K)).toMonoidHom) at hc
    have heV : U.map
        (MulAut.conj (CFSGNormTwoGeckFieldOpposition.oppositionUnit A hs hp b₀ K)).toMonoidHom = V :=
      opposition_positive_eq_negative A hs hp b₀ s₀ K
    rw [heV] at hc
    exact hc.symm.trans (positive_card A hd hs hp ho K)
  calc
    Nat.card K ^ (2 * Nat.card (PositiveRoot A)) = Nat.card UH * Nat.card VH := by
      rw [hUcard, hVcard, ← pow_add, two_mul]
    _ ≤ Nat.card (Projective (cartan b₀ s₀) K) := hh

end SymmetricSubgroupAsymptotics.CFSGNormTwoCoordinateOriginalOrderLower
