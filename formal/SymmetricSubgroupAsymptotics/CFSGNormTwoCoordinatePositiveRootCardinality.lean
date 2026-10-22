import SymmetricSubgroupAsymptotics.CFSGNormTwoCoordinateRootHeightLeading
import SymmetricSubgroupAsymptotics.CFSGNormTwoCoordinateRootHeightCommutator
import SymmetricSubgroupAsymptotics.CFSGNormTwoCoordinateRootElementRange
import SymmetricSubgroupAsymptotics.CFSGNormTwoCoordinateSelectedRootAdditive

/-! Literal positive root parameters are injective over every field,
and the actual positive root subgroup has cardinality exactly the field
cardinality. The primitive first integer-degree coefficient proves this. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGNormTwoCoordinatePositiveRootCardinality
open CFSGIntegerMatrixPairing CFSGNormTwoRootPairing
open CFSGNormTwoCoordinateRootHeightLeading CFSGNormTwoCoordinateRootHeightCommutator
open CFSGNormTwoCoordinateRootBracketTransport CFSGNormTwoCoordinateRootElementRange
open CFSGNormTwoCoordinateRootSubgroup CFSGNormTwoCoordinateSelectedRootAdditive
open CFSGNormTwoCoordinateSelectedRootElement CFSGGradedMatrixSingleDegreeSpan
variable {r : ℕ} (A : Matrix (Fin r) (Fin r) ℤ) (hd : ∀i,A i i=2)
    (hs : A.transpose=A) (hp : (rationalMatrix A).PosDef)
    (ho : ∀i j,i≠j→A i j≤0)
    [Fintype (Roots A)] [DecidableEq (Roots A)]
    [(rootPairing A hs hp).IsReduced] [(rootPairing A hs hp).IsIrreducible]
local notation "b₀" => coordinateBase A hd hs hp ho
private abbrev CoordMat (K : Type) := Matrix ((b₀).support⊕Roots A) ((b₀).support⊕Roots A) K

theorem selectedRootHom_range (K : Type) [Field K] (k : Roots A) :
    (selectedRootHom A hd hs hp ho K k).range=rootSubgroup A hd hs hp ho K k := by
  apply Subgroup.ext
  intro x
  rw [mem_rootSubgroup_iff_selected]
  constructor
  · rintro ⟨a,ha⟩
    exact ⟨a.toAdd,ha⟩
  · rintro ⟨a,ha⟩
    exact ⟨Multiplicative.ofAdd a,ha⟩

theorem selected_positive_rootHom_injective (K : Type) [Field K] (k : Roots A)
    (hk : ∀i,0≤k.val i) : Function.Injective (selectedRootHom A hd hs hp ho K k) := by
  intro a b he
  change selectedRootElement A hd hs hp ho K k a.toAdd=selectedRootElement A hd hs hp ho K k b.toAdd at he
  have hh := positive_root_height_pos A k hk
  have hp' := congrArg (fun u : (CoordMat A hd hs hp ho K)ˣ=>
    degreePart (heightWeight A hd hs hp ho) (CFSGIntegerHeightSign.height k.val)
      ((u : CoordMat A hd hs hp ho K)-1)) he
  dsimp only at hp'
  rw [(selected_root_cut_and_leading A hd hs hp ho K k hh a.toAdd).2,
    (selected_root_cut_and_leading A hd hs hp ho K k hh b.toAdd).2] at hp'
  have hab : a.toAdd=b.toAdd := smul_left_injective K
    (selectedFieldCoefficient_ne_zero A hd hs hp ho K k) hp'
  exact congrArg Multiplicative.ofAdd hab

theorem positive_rootSubgroup_card (K : Type) [Field K] (k : Roots A) (hk : ∀i,0≤k.val i) :
    Nat.card (rootSubgroup A hd hs hp ho K k)=Nat.card K := by
  rw [←selectedRootHom_range]
  calc
    _=Nat.card (Multiplicative K) := (Nat.card_congr
      (MonoidHom.ofInjective (selected_positive_rootHom_injective A hd hs hp ho K k hk)).toEquiv).symm
    _=Nat.card K := Nat.card_congr (Multiplicative.toAdd : Multiplicative K≃K)

end SymmetricSubgroupAsymptotics.CFSGNormTwoCoordinatePositiveRootCardinality
