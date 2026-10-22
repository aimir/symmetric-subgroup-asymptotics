import SymmetricSubgroupAsymptotics.CFSGNormTwoCoordinateOriginalOppositePairData
import SymmetricSubgroupAsymptotics.CFSGOppositeSylowPairAlignment

/-! Every actual automorphism of the original simple projective Serre
group can be adjusted by an actual inner automorphism to preserve BOTH
literal positive and negative subgroups. No automorphism lift is used. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Pointwise
namespace SymmetricSubgroupAsymptotics.CFSGNormTwoCoordinateOriginalPairAlignment
open CFSG.Models.Chevalley CFSGIntegerMatrixPairing CFSGNormTwoRootPairing
open CFSGGeckSerreRepresentation CFSGNormTwoGeckIntegralRealization
open CFSGNormTwoGeckWeylWordDegree CFSGNormTwoGeckWeylLatticeLinear
open CFSGNormTwoGeckPositivePGroup CFSGNormTwoCoordinateOriginalPositiveCenter
open CFSGNormTwoCoordinateOriginalPositiveSylow CFSGNormTwoCoordinateOriginalRootFamily
open CFSGNormTwoCoordinateOriginalOppositeAlignment CFSGNormTwoCoordinateOriginalOppositePairData
variable {r : ℕ} (A : Matrix (Fin r) (Fin r) ℤ) (hd : ∀j,A j j=2)
    (hs : A.transpose=A) (hp : (rationalMatrix A).PosDef)
    (ho : ∀i j,i≠j→A i j≤0)
    [Fintype (Roots A)] [DecidableEq (Roots A)]
    [(rootPairing A hs hp).IsReduced] [(rootPairing A hs hp).IsIrreducible]
    (K : Type) [Field K] [Finite K] [Nontrivial (Fin r)]
local notation "b₀" => coordinateBase A hd hs hp ho
local notation "s₀" => coordinateIndexEquiv A hd hs hp ho

theorem original_exists_inner_fix_pair
    (ε : Fin r→ℤ) (hε : ∀j,ε j*ε j=1) (hA : ∀i j,ε i*|A i j|=A j i*ε j)
    (hidentity : ∀w : List (Fin r),wordUnit A hs hp b₀ s₀ K w∈
      Subgroup.normalizer (rootGroup A hs hp b₀ s₀ K false : Set _)→wordLinear A hs hp b₀ s₀ w=1)
    (p : ℕ) [Fact p.Prime] [CharP K p]
    [IsSimpleGroup (Projective (cartan b₀ s₀) K)] (i : Fin r)
    (f : MulAut (Projective (cartan b₀ s₀) K)) :
    ∃g : Projective (cartan b₀ s₀) K,
      (originalPositive A hd hs hp ho K i).map (MulAut.conj g*f).toMonoidHom=
        originalPositive A hd hs hp ho K i ∧
      (originalNegative A hd hs hp ho K i).map (MulAut.conj g*f).toMonoidHom=
        originalNegative A hd hs hp ho K i := by
  let G := Projective (cartan b₀ s₀) K
  letI : Finite G := original_projective_finite A hd hs hp ho K i
  let P := originalPositiveSylow A hd hs hp ho K ε hε hA hidentity p i
  have hP : (P : Subgroup G)=originalPositive A hd hs hp ho K i :=
    originalPositiveSylow_coe A hd hs hp ho K ε hε hA hidentity p i
  obtain ⟨hdisj,hcard⟩ := original_opposite_disjoint_and_card A hd hs hp ho K
    ε hε hA hidentity p i
  have horder : Nat.card (originalNegative A hd hs hp ho K i)=p^(Nat.card G).factorization p := by
    rw [hcard,←hP]
    exact P.card_eq_multiplicity
  let Q : Sylow p G := Sylow.ofCard (originalNegative A hd hs hp ho K i) horder
  have hQ : (Q : Subgroup G)=originalNegative A hd hs hp ho K i := Sylow.coe_ofCard _ _
  obtain ⟨g,hgP,hgQ⟩ := CFSGOppositeSylowPairAlignment.exists_inner_fix_pair P Q
    (by rw [hP,hQ]; exact hdisj) (fun a ha=>by
      rw [hP] at ha
      obtain ⟨b,hb,he⟩ := original_opposite_conjugate_by_borel A hd hs hp ho K p i a ha
      refine ⟨b,?_,?_⟩
      · change b∈Subgroup.normalizer (P : Set G)
        rw [show (P : Set G)=(originalPositive A hd hs hp ho K i : Set G) from
          congrArg (fun S : Subgroup G=>(S : Set G)) hP]
        exact originalBorel_le_normalizer_positive A hd hs hp ho K i hb
      · rw [hP,hQ]
        exact he) f
  refine ⟨g,?_,?_⟩
  · have hh := congrArg (fun R : Sylow p G=>(R : Subgroup G)) hgP
    change (P : Subgroup G).map (MulAut.conj g*f).toMonoidHom=(P : Subgroup G) at hh
    simpa only [hP] using hh
  · have hh := congrArg (fun R : Sylow p G=>(R : Subgroup G)) hgQ
    change (Q : Subgroup G).map (MulAut.conj g*f).toMonoidHom=(Q : Subgroup G) at hh
    simpa only [hQ] using hh

end SymmetricSubgroupAsymptotics.CFSGNormTwoCoordinateOriginalPairAlignment
