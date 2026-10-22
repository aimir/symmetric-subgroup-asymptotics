import SymmetricSubgroupAsymptotics.CFSGNormTwoCoordinateRootFamilyCardinality
import SymmetricSubgroupAsymptotics.CFSGNormTwoCoordinateOriginalAllRootLines
import SymmetricSubgroupAsymptotics.CFSGRangeFactorCardinality

/-! Push the ACTUAL matrix root-family bound through the original
projective quotient. No faithfulness or lifting of automorphisms is used. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGNormTwoCoordinateOriginalRootFamilyCardinality
open CFSG.Models.Chevalley CFSGIntegerMatrixPairing CFSGNormTwoRootPairing
open CFSGGeckSerreRepresentation CFSGNormTwoCoordinateElementaryRootParameters
open CFSGNormTwoCoordinateOriginalAllRootLines CFSGNormTwoCoordinateOriginalProjection
open CFSGNormTwoCoordinateOriginalRootFamily CFSGNormTwoCoordinateRootSubgroup
open CFSGNormTwoCoordinateRootElementRange CFSGSubgroupConjugateRestriction
open CFSGNormTwoCoordinateRootFamilyCardinality CFSGNormTwoCoordinateRootCentralizerCardinality
open CFSGNormTwoCoordinatePositiveRootGenerators CFSGRangeFactorCardinality
variable {r : ℕ} (A : Matrix (Fin r) (Fin r) ℤ) (hd : ∀ i, A i i = 2)
    (hs : A.transpose = A) (hp : (rationalMatrix A).PosDef)
    (ho : ∀ i j, i ≠ j → A i j ≤ 0)
    [Fintype (Roots A)] [DecidableEq (Roots A)]
    [(rootPairing A hs hp).IsReduced] [(rootPairing A hs hp).IsIrreducible]
    (K : Type) [Field K]
local notation "b₀" => coordinateBase A hd hs hp ho
local notation "s₀" => coordinateIndexEquiv A hd hs hp ho

def originalRootFamily [IsSimpleGroup (Projective (cartan b₀ s₀) K)]
    (i : Fin r) (θ : Roots A) := Set.range (originalConjugateRootLine A hd hs hp ho K i θ)

theorem original_root_family_card_le [Finite K]
    [IsSimpleGroup (Projective (cartan b₀ s₀) K)] (i : Fin r) (θ : Roots A)
    (hθ : ∀ j, 0 ≤ θ.val j) :
    Nat.card (originalRootFamily A hd hs hp ho K i θ) ≤
      Nat.card (rootConjugateFamily A hd hs hp ho K θ) := by
  let H := ElementaryGroup A hd hs hp ho K
  let R := rootSubgroup A hd hs hp ho K θ
  let R0 := elementaryRootSubgroup A hd hs hp ho K θ
  let f := originalProjection A hd hs hp ho K i
  let F (g : H) := R.map (MulAut.conj g.val).toMonoidHom
  let G (g : H) := originalConjugateRootLine A hd hs hp ho K i θ (f g)
  have hR : R0.map H.subtype = R :=
    Subgroup.map_subgroupOf_eq_of_le (rootSubgroup_le_elementary A hd hs hp ho K θ)
  have hRf : R0.map f = originalRootLine A hd hs hp ho K i θ :=
    originalFullRootLine_eq_positive A hd hs hp ho K i θ hθ
  have hfactor : ∀ g h : H, F g = F h → G g = G h := by
    intro g h he
    have hsub : (R0.map (MulAut.conj g).toMonoidHom).map H.subtype =
        (R0.map (MulAut.conj h).toMonoidHom).map H.subtype := by
      rw [map_conjugate, map_conjugate, hR]
      exact he
    have hS := Subgroup.map_injective H.subtype_injective hsub
    have hh := congrArg (fun S : Subgroup H => S.map f) hS
    change (originalRootLine A hd hs hp ho K i θ).map (MulAut.conj (f g)).toMonoidHom =
      (originalRootLine A hd hs hp ho K i θ).map (MulAut.conj (f h)).toMonoidHom
    simpa only [map_conjugate, hRf] using hh
  have hG : Set.range G = originalRootFamily A hd hs hp ho K i θ := by
    exact (originalProjection_surjective A hd hs hp ho K i).range_comp
      (originalConjugateRootLine A hd hs hp ho K i θ)
  calc
    _ = Nat.card (Set.range G) := by rw [hG]
    _ ≤ Nat.card (Set.range F) := card_range_le_of_factor F G hfactor
    _ = _ := rfl

theorem original_root_family_card_mul_uniform_commuting_le [Finite K]
    [IsSimpleGroup (Projective (cartan b₀ s₀) K)] (i : Fin r)
    (θ : Roots A) (hθ : ∀ j, 0 ≤ θ.val j)
    (hdom : ∀ j, 0 ≤ integerPairing A θ.val (Pi.single j (1 : ℤ) : Fin r → ℤ))
    (c : ℕ) (hc : ∀ k : Roots A, c ≤ (commutingPositiveRoots A k).card) :
    Nat.card (originalRootFamily A hd hs hp ho K i θ) * Nat.card K ^ c ≤
      Nat.card (Roots A) * Nat.card K ^ Nat.card (PositiveRoot A) :=
  (Nat.mul_le_mul_right _ (original_root_family_card_le A hd hs hp ho K i θ hθ)).trans
    (root_family_card_mul_uniform_commuting_le A hd hs hp ho K θ hθ hdom c hc)

end SymmetricSubgroupAsymptotics.CFSGNormTwoCoordinateOriginalRootFamilyCardinality
