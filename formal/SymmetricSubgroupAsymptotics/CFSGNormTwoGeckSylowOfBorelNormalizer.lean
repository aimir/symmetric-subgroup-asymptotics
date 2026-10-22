import SymmetricSubgroupAsymptotics.CFSGNormTwoGeckBorelPowerElements
import SymmetricSubgroupAsymptotics.CFSGSylowNormalizerMaximality

/-! The exact remaining normalizer seam, restricted to the ACTUAL
canonical group. Once that containment is proved, the literal positive
subgroup is Sylow and has soluble normalizer. No containment is asserted
by this installer, and ambient scalar normalizers are not discarded. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGNormTwoGeckSylowOfBorelNormalizer
open CFSGIntegerMatrixPairing CFSGNormTwoRootPairing
open CFSGNormTwoGeckIntegralRealization CFSGSerreQuadraticMatrix
open CFSGNormTwoGeckPositivePGroup CFSGNormTwoGeckBorelEnvelope
open CFSGNormTwoGeckBorelPowerElements
variable {n : Type} [Fintype n] [DecidableEq n]
    (A : Matrix n n ℤ) (hs : A.transpose=A) (hp : (rationalMatrix A).PosDef)
    [Fintype (Roots A)] [DecidableEq (Roots A)] [(rootPairing A hs hp).IsIrreducible]
    (b : (rootPairing A hs hp).Base) {r : ℕ} (s : Fin r≃b.support)
    (K : Type) [Field K]

abbrev H := canonicalElementaryGroup (realizationData A hs hp b s) K
abbrev U := rootGroup A hs hp b s K false
abbrev B := borelEnvelope A hs hp b s K

theorem positive_le_canonical : U A hs hp b s K≤H A hs hp b s K := by
  change rootGroup A hs hp b s K false≤canonicalElementaryGroup (realizationData A hs hp b s) K
  rw [←positive_sup_negative A hs hp b s K]
  exact le_sup_left

theorem normalizer_positive_map_le_borel
    (hN : Subgroup.normalizer (U A hs hp b s K : Set _)⊓H A hs hp b s K≤B A hs hp b s K) :
    (Subgroup.normalizer ((U A hs hp b s K).subgroupOf (H A hs hp b s K) :
      Set (H A hs hp b s K))).map (H A hs hp b s K).subtype≤B A hs hp b s K := by
  let UH := (U A hs hp b s K).subgroupOf (H A hs hp b s K)
  have hm : UH.map (H A hs hp b s K).subtype=U A hs hp b s K := by
    rw [Subgroup.subgroupOf_map_subtype,inf_of_le_left (positive_le_canonical A hs hp b s K)]
  intro x hx
  have hn := UH.le_normalizer_map (H A hs hp b s K).subtype hx
  rw [hm] at hn
  have hh : x∈H A hs hp b s K := by
    obtain ⟨y,_,rfl⟩ := hx
    exact y.property
  exact hN ⟨hn,hh⟩

def positiveSylowOfBorelNormalizer [Finite K]
    (height : (n→ℤ)→ₗ[ℤ]ℤ) (hheight : ∀i : b.support,height (i:Roots A).val=1)
    (p : ℕ) [Fact p.Prime] [CharP K p]
    (hN : Subgroup.normalizer (U A hs hp b s K : Set _)⊓H A hs hp b s K≤B A hs hp b s K) :
    Sylow p (H A hs hp b s K) := by
  let UH := (U A hs hp b s K).subgroupOf (H A hs hp b s K)
  have hUp : IsPGroup p UH :=
    (positive_isPGroup A hs hp b s height hheight K p).of_injective
      (Subgroup.subgroupOfEquivOfLe (positive_le_canonical A hs hp b s K)).toMonoidHom
      (Subgroup.subgroupOfEquivOfLe (positive_le_canonical A hs hp b s K)).injective
  apply CFSGSylowNormalizerMaximality.sylowOfNormalizer UH hUp
  intro P hP hPN
  have hPB : P.map (H A hs hp b s K).subtype≤B A hs hp b s K :=
    (Subgroup.map_mono hPN).trans (normalizer_positive_map_le_borel A hs hp b s K hN)
  have hPU := pSubgroup_le_positive A hs hp b s height hheight K p _
    (hP.map (H A hs hp b s K).subtype) hPB
  intro x hx
  exact hPU ⟨x,hx,rfl⟩

theorem positive_normalizer_soluble
    (height : (n→ℤ)→ₗ[ℤ]ℤ) (hheight : ∀i : b.support,height (i:Roots A).val=1)
    (hN : Subgroup.normalizer (U A hs hp b s K : Set _)⊓H A hs hp b s K≤B A hs hp b s K) :
    IsSolvable (Subgroup.normalizer ((U A hs hp b s K).subgroupOf (H A hs hp b s K) :
      Set (H A hs hp b s K))) := by
  let N := Subgroup.normalizer ((U A hs hp b s K).subgroupOf (H A hs hp b s K) :
    Set (H A hs hp b s K))
  let f : N→*B A hs hp b s K :=
    { toFun:=fun x=>⟨x.val.val,normalizer_positive_map_le_borel A hs hp b s K hN
        ⟨x.val,x.property,rfl⟩⟩
      map_one':=rfl
      map_mul':=fun _ _=>rfl }
  letI : IsSolvable (B A hs hp b s K) := borelEnvelope_soluble A hs hp b s height hheight K
  apply solvable_of_solvable_injective (f:=f)
  intro x y h
  dsimp only [f] at h
  apply Subtype.ext
  apply Subtype.ext
  exact congrArg (fun z : B A hs hp b s K=>z.val) h

end SymmetricSubgroupAsymptotics.CFSGNormTwoGeckSylowOfBorelNormalizer
