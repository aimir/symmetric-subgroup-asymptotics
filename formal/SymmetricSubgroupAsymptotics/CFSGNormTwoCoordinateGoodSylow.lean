import SymmetricSubgroupAsymptotics.CFSGNormTwoCoordinateNormalizerDiagonalFactor
import SymmetricSubgroupAsymptotics.CFSGNormTwoGeckSylowOfBorelNormalizer
import SymmetricSubgroupAsymptotics.CFSGGoodSylowFromPositiveNormalizer

/-! Actual good defining-prime Sylow data for the original coordinate
matrix group, from proved literal normalizing-word lattice identities.
No normalizer=B or named finite-group recognition premise occurs. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGNormTwoCoordinateGoodSylow
open CFSGIntegerMatrixPairing CFSGNormTwoRootPairing CFSGSerreQuadraticMatrix
open CFSGNormTwoGeckIntegralRealization CFSGNormTwoGeckPositivePGroup
open CFSGNormTwoGeckWeylWordDegree CFSGNormTwoGeckWeylLatticeLinear
open CFSGNormTwoCoordinateNormalizerDiagonalFactor CFSGNormTwoCoordinateHeight
open CFSGNormTwoGeckBorelPowerElements CFSGNormTwoGeckHeightSupport
open CFSGNormTwoGeckSylowOfBorelNormalizer
variable {r : ℕ} (A : Matrix (Fin r) (Fin r) ℤ) (hd : ∀j,A j j=2)
    (hs : A.transpose=A) (hp : (rationalMatrix A).PosDef)
    (ho : ∀i j,i≠j→A i j≤0)
    [Fintype (Roots A)] [DecidableEq (Roots A)] [(rootPairing A hs hp).IsIrreducible]

local notation "b₀" => coordinateBase A hd hs hp ho
local notation "s₀" => coordinateIndexEquiv A hd hs hp ho

theorem canonical_goodSylowPrime (K : Type) [Field K] [Finite K]
    (ε : Fin r→ℤ) (hε : ∀i,ε i*ε i=1)
    (hA : ∀i j,ε i*|A i j|=A j i*ε j)
    (hidentity : ∀w : List (Fin r),wordUnit A hs hp b₀ s₀ K w∈
      Subgroup.normalizer (rootGroup A hs hp b₀ s₀ K false : Set _)→
      wordLinear A hs hp b₀ s₀ w=1)
    (p : ℕ) [Fact p.Prime] [CharP K p] :
    CFSGReduction.GoodSylowPrime (canonicalElementaryGroup (realizationData A hs hp b₀ s₀) K) p := by
  letI : Fintype K := Fintype.ofFinite K
  let H := canonicalElementaryGroup (realizationData A hs hp b₀ s₀) K
  let U := rootGroup A hs hp b₀ s₀ K false
  let V := rootGroup A hs hp b₀ s₀ K true
  have hjoin : U⊔V=H := positive_sup_negative A hs hp b₀ s₀ K
  have hUH : U≤H := by rw [←hjoin];exact le_sup_left
  have hVH : V≤H := by rw [←hjoin];exact le_sup_right
  let UH := U.subgroupOf H
  let VH := V.subgroupOf H
  have hm : UH.map H.subtype=U := by
    rw [Subgroup.subgroupOf_map_subtype,inf_of_le_left hUH]
  have hnormal : (Subgroup.normalizer (UH : Set H)).map H.subtype≤
      Subgroup.normalizer (U : Set _) ⊓ H := by
    intro g hg
    have hn := UH.le_normalizer_map H.subtype hg
    rw [hm] at hn
    refine ⟨hn,?_⟩
    obtain ⟨x,_,rfl⟩ := hg
    exact x.property
  have hUp : IsPGroup p UH :=
    (positive_isPGroup A hs hp b₀ s₀ coordinateHeight (simple_height A hd hs hp ho) K p).of_injective
      (Subgroup.subgroupOfEquivOfLe hUH).toMonoidHom (Subgroup.subgroupOfEquivOfLe hUH).injective
  have hVp : IsPGroup p VH :=
    (negative_isPGroup A hs hp b₀ s₀ coordinateHeight (simple_height A hd hs hp ho) K p).of_injective
      (Subgroup.subgroupOfEquivOfLe hVH).toMonoidHom (Subgroup.subgroupOfEquivOfLe hVH).injective
  have hgen : UH⊔VH=⊤ := by
    rw [←Subgroup.subgroupOf_sup hUH hVH,hjoin,Subgroup.subgroupOf_self]
  have hmax : ∀P : Subgroup H,IsPGroup p P→P≤Subgroup.normalizer (UH : Set H)→P≤UH := by
    intro P hP hPN
    have hmap : P.map H.subtype≤Subgroup.normalizer (U : Set _) ⊓ H :=
      (Subgroup.map_mono hPN).trans hnormal
    have hle := pSubgroup_normalizer_le_positive A hd hs hp ho K ε hε hA hidentity p
      (P.map H.subtype) (hP.map H.subtype) (le_trans hmap inf_le_right)
      (le_trans hmap inf_le_left)
    intro x hx
    exact hle ⟨x,hx,rfl⟩
  let N : Subgroup ((Matrix ((b₀).support⊕Roots A) ((b₀).support⊕Roots A) K)ˣ) :=
    Subgroup.normalizer (U : Set _) ⊓ H
  obtain ⟨e,he⟩ := CFSGFiniteWeightFlag.exists_flag (weight A hs hp b₀ coordinateHeight)
  letI : IsSolvable N := CFSGDiagonalUnipotentExtension.subgroup_soluble e N U
    (positive_le_unipotent A hs hp b₀ s₀ coordinateHeight (simple_height A hd hs hp ho) K e he)
    (fun g hg=>normalizer_diagonal_factor A hd hs hp ho K ε hε hA hidentity g hg.2 hg.1)
  let NH := Subgroup.normalizer (UH : Set H)
  let f : NH→*N :=
    { toFun := fun x=>⟨x.val.val,hnormal ⟨x.val,x.property,rfl⟩⟩
      map_one' := rfl
      map_mul' := fun _ _=>rfl }
  have hf : Function.Injective f := by
    intro x y h
    dsimp only [f] at h
    apply Subtype.ext
    apply Subtype.ext
    exact congrArg (fun z : N=>z.val) h
  have hsol : IsSolvable NH := solvable_of_solvable_injective (f:=f) hf
  exact CFSGReduction.goodSylowPrime_of_positive_normalizer UH VH hUp hVp hgen hmax hsol

end SymmetricSubgroupAsymptotics.CFSGNormTwoCoordinateGoodSylow
