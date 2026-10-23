import SymmetricSubgroupAsymptotics.CFSGE6GeckFixedCoordinateCardinality
import SymmetricSubgroupAsymptotics.CFSGFFourE6FixedPositive
import SymmetricSubgroupAsymptotics.CFSGE6FixedPositiveRootMenu
import SymmetricSubgroupAsymptotics.FiniteWeightedTailCardinality

/-! The actual diagram-fixed E6 upper subgroup has at most |K|^24
elements. Squared fixed-coordinate bounds telescope through the genuine
height filtration. The only census inputs are the checked 36 positive
roots and at most 12 diagram-fixed positive roots. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics.CFSGFFourE6FixedPositiveCardinality
open CFSGE6GeckFixedTailCardinality CFSGE6GeckFixedCoordinateCardinality
open CFSGTwistedE6GeckHeightRootPermutation CFSGTwistedE6DiagramRootOrthogonality
open CFSGTwistedE6GeckPositiveTwist CFSGTwistedE6GeckFixedPositiveSourceImage
open CFSGTwistedE6GeckHeightQuotientTwist
open CFSGNormTwoRootPairing CFSGNormTwoCoordinatePositiveRootGenerators
open CFSGNormTwoCoordinateRootHeightBound CFSGNormTwoCoordinateRootHeightCommutator
open CFSGTwistedE6WeylChamber CFSGIntegerHeightSign

private abbrev DiagramFixedPositive :=
  {k:PositiveRoot CartanMatrix.E₆ // diagramRoot k.val=k.val}

private def fixedHeightEquiv (h:ℤ) :
    {k:HeightIndex h // heightRootPermutation h k=k}≃
      {k:DiagramFixedPositive // height k.val.val.val=h} where
  toFun k:=⟨⟨k.val.val,congrArg (fun j:HeightIndex h=>j.val.val) k.property⟩,k.val.property⟩
  invFun k:=⟨⟨k.val.val,k.property⟩,by
    apply Subtype.ext
    apply Subtype.ext
    exact k.val.property⟩
  left_inv _:=rfl
  right_inv _:=rfl

private theorem fixedPositiveRoots_card_le : Nat.card DiagramFixedPositive≤12 := by
  let f : DiagramFixedPositive→{k:PositiveRoot CartanMatrix.E₆ //
      ∀i,k.val.val (CFSG.Models.e6Twist i)=k.val.val i} := fun k=>⟨k.val,by
    intro i
    have he := congrArg (fun r:Roots CartanMatrix.E₆=>r.val i) k.property
    dsimp only at he
    rw [diagramRoot_coordinate] at he
    exact he⟩
  have hi : Function.Injective f := by
    intro a b he
    have hv : a.val=b.val := congrArg (fun k:{k:PositiveRoot CartanMatrix.E₆ //
      ∀i,k.val.val (CFSG.Models.e6Twist i)=k.val.val i}=>k.val) he
    exact Subtype.ext hv
  exact (Nat.card_le_card_of_injective f hi).trans
    CFSGE6FixedPositiveRootMenu.fixed_positive_root_card_le

theorem fixedPositive_card_sq_le (K:Type) [Field K] [Finite K] (sigma:K≃+*K) :
    Nat.card (CFSGE6GeckFixedTailCardinality.fixedPositive K sigma)^2≤
      Nat.card K^(Nat.card (PositiveRoot CartanMatrix.E₆)+Nat.card DiagramFixedPositive) := by
  let a : ℤ→ℕ := fun h=>Nat.card (fixedTail K sigma h)
  have hend : a ((rootHeightBound CartanMatrix.E₆:ℤ)+1)=1 := by
    simp [a,fixedTail,terminal_tail_eq_bot]
    exact inf_eq_left.mpr bot_le
  have hstep (h:ℤ) (hh:0<h) :
      a h^2≤Nat.card K^(Nat.card {x:PositiveRoot CartanMatrix.E₆ // height x.val.val=h}+
        Nat.card {x:DiagramFixedPositive // height x.val.val.val=h})*a (h+1)^2 := by
    have hc := CFSGE6GeckFixedCoordinateCardinality.fixedCoordinates_card_sq_le K sigma h hh
    rw [Nat.card_congr (fixedHeightEquiv h)] at hc
    exact (fixedTail_card_sq_step K sigma h hh).trans
      (Nat.mul_le_mul_right _ hc)
  have hp (k:PositiveRoot CartanMatrix.E₆) : 1≤height k.val.val := by
    have hh := positive_root_height_pos CartanMatrix.E₆ k.val k.property
    omega
  have hb := FiniteWeightedTailCardinality.square_bound_of_degree_steps
    (PositiveRoot CartanMatrix.E₆) DiagramFixedPositive
    (fun k=>height k.val.val) (fun k=>height k.val.val.val) hp (fun k=>hp k.val)
    (Nat.card K) (rootHeightBound CartanMatrix.E₆) (Nat.card_pos (α:=K)) a hend hstep
  have hfirst : a 1=Nat.card (CFSGE6GeckFixedTailCardinality.fixedPositive K sigma) := by
    dsimp only [a,fixedTail]
    rw [first_tail_eq_top]
    have he : ((⊤:Subgroup (Positive K))⊓CFSGE6GeckFixedTailCardinality.fixedPositive K sigma)=
        CFSGE6GeckFixedTailCardinality.fixedPositive K sigma := inf_eq_right.mpr le_top
    exact congrArg (fun S:Subgroup (Positive K)=>Nat.card S) he
  simpa only [hfirst] using hb

theorem fixedPositive_card_le (K:Type) [Field K] [Finite K] (sigma:K≃+*K) :
    Nat.card (CFSGE6GeckFixedTailCardinality.fixedPositive K sigma)≤Nat.card K^24 := by
  have he : Nat.card (PositiveRoot CartanMatrix.E₆)+Nat.card DiagramFixedPositive≤48 :=
    Nat.add_le_add CFSGE6FiniteRootMenu.positive_roots_card_le fixedPositiveRoots_card_le
  have hs := (fixedPositive_card_sq_le K sigma).trans
    (Nat.pow_le_pow_right (Nat.card_pos (α:=K)) he)
  apply le_of_pow_le_pow_left₀ (by decide : (2:ℕ)≠0) (Nat.zero_le (Nat.card K^24))
  exact hs.trans_eq (by rw [←pow_mul])

theorem fixedUpper_card_le (K:Type) [Field K] [Finite K] :
    Nat.card (CFSGFFourE6FixedPositive.fixedUpper K)≤Nat.card K^24 :=
  fixedPositive_card_le K (RingEquiv.refl K)

end SymmetricSubgroupAsymptotics.CFSGFFourE6FixedPositiveCardinality
