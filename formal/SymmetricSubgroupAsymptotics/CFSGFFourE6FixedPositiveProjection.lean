import SymmetricSubgroupAsymptotics.CFSGFFourE6OriginalProjection
import SymmetricSubgroupAsymptotics.CFSGFFourE6FixedPositive
import SymmetricSubgroupAsymptotics.CFSGTwistedE6GeckRelativeRootGenerated
import Mathlib.Tactic.Linarith

/-! The literal identity-field diagram-fixed E6 upper subgroup is in
bijection with the named folded F4 positive Sylow. Its projection to the
ORIGINAL F4 model is injective, with the strict square order margin. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics.CFSGFFourE6FixedPositiveProjection
open CFSGFFourSerreMatrices CFSGFFourE6OriginalProjection CFSGFFourE6FixedPositive
open CFSGFFourE6FixedHeightLifting CFSGFFourE6DiagramFixed CFSGFFourE6PositiveSylow
open CFSGFFourE6ProjectiveOrder CFSGTwistedE6GeckRelativeRootGenerated
open CFSGTwistedE6GeckPositiveTwist CFSGSerreQuadraticMatrix CFSG.Models.Chevalley

theorem fixedPositive_mem_folded (K : Type) [Field K] [Finite K]
    (u : signedFixed K (RingEquiv.refl K) false) :
    u.val∈canonicalElementaryGroup realizationData K := by
  let x : Positive K := ⟨u.val,u.property.1⟩
  have hfix : positiveTwist K (RingEquiv.refl K) x=x := Subtype.ext u.property.2
  have hm : x∈foldedUpper K := (le_of_eq (fixedUpper_eq_foldedUpper K)) hfix
  exact hm

def fixedPositiveToFolded (K : Type) [Field K] [Finite K] :
    signedFixed K (RingEquiv.refl K) false→*canonicalElementaryGroup realizationData K where
  toFun u := ⟨u.val,fixedPositive_mem_folded K u⟩
  map_one' := rfl
  map_mul' _ _ := rfl

def fixedPositiveToSylow (K : Type) [Field K] [Finite K]
    (p : ℕ) [Fact p.Prime] [CharP K p] :
    signedFixed K (RingEquiv.refl K) false→*positiveSylow K p :=
  (fixedPositiveToFolded K).codRestrict
    (positiveSylow K p : Subgroup (canonicalElementaryGroup realizationData K)) (fun u=>by
      rw [positiveSylow_coe]
      exact u.property.1)

theorem fixedPositiveToSylow_injective (K : Type) [Field K] [Finite K]
    (p : ℕ) [Fact p.Prime] [CharP K p] : Function.Injective (fixedPositiveToSylow K p) := by
  intro u v he
  exact Subtype.ext (congrArg (fun z : positiveSylow K p=>z.val.val) he)

theorem fixedPositiveToSylow_surjective (K : Type) [Field K] [Finite K]
    (p : ℕ) [Fact p.Prime] [CharP K p] : Function.Surjective (fixedPositiveToSylow K p) := by
  intro x
  have hpos : x.val.val∈Positive K := (le_of_eq (positiveSylow_coe K p)) x.property
  have hfix := foldedModel_le_diagramFixed K x.val.property
  refine ⟨⟨x.val.val,⟨hpos,hfix⟩⟩,?_⟩
  apply Subtype.ext
  apply Subtype.ext
  rfl

def fixedPositiveSylowEquiv (K : Type) [Field K] [Finite K]
    (p : ℕ) [Fact p.Prime] [CharP K p] :
    signedFixed K (RingEquiv.refl K) false≃*positiveSylow K p :=
  MulEquiv.ofBijective (fixedPositiveToSylow K p)
    ⟨fixedPositiveToSylow_injective K p,fixedPositiveToSylow_surjective K p⟩

def fixedPositiveToOriginal (K : Type) [Field K] [Finite K]
    (p : ℕ) [Fact p.Prime] [CharP K p] [IsSimpleGroup (Projective CartanMatrix.F₄ K)] :
    signedFixed K (RingEquiv.refl K) false→*Projective CartanMatrix.F₄ K :=
  (foldedPositiveToOriginal K p).comp (fixedPositiveToSylow K p)

theorem fixedPositiveToOriginal_apply (K : Type) [Field K] [Finite K]
    (p : ℕ) [Fact p.Prime] [CharP K p] [IsSimpleGroup (Projective CartanMatrix.F₄ K)]
    (u : signedFixed K (RingEquiv.refl K) false) :
    fixedPositiveToOriginal K p u=foldedToOriginal K (fixedPositiveToFolded K u) := rfl

theorem fixedPositiveToOriginal_injective (K : Type) [Field K] [Finite K]
    (p : ℕ) [Fact p.Prime] [CharP K p] [IsSimpleGroup (Projective CartanMatrix.F₄ K)] :
    Function.Injective (fixedPositiveToOriginal K p) :=
  (foldedPositiveToOriginal_injective K p).comp (fixedPositiveToSylow_injective K p)

theorem fixedPositive_square_lt_original_order (K : Type) [Field K] [Finite K]
    (p : ℕ) [Fact p.Prime] [CharP K p] [IsSimpleGroup (Projective CartanMatrix.F₄ K)] :
    Nat.card (signedFixed K (RingEquiv.refl K) false)^2<
      Nat.card (Projective CartanMatrix.F₄ K) := by
  rw [Nat.card_congr (fixedPositiveSylowEquiv K p).toEquiv]
  exact serreTypeFFour_positive_square_lt_order K p

def originalFixedPositive (K : Type) [Field K] [Finite K]
    (p : ℕ) [Fact p.Prime] [CharP K p] [IsSimpleGroup (Projective CartanMatrix.F₄ K)] :
    Subgroup (Projective CartanMatrix.F₄ K) := (fixedPositiveToOriginal K p).range

theorem originalFixedPositive_ne_top (K : Type) [Field K] [Finite K]
    (p : ℕ) [Fact p.Prime] [CharP K p] [IsSimpleGroup (Projective CartanMatrix.F₄ K)] :
    originalFixedPositive K p≠⊤ := by
  letI : Finite (Projective CartanMatrix.F₄ K) := original_finite K
  intro htop
  have hc := Nat.card_congr (MonoidHom.ofInjective (fixedPositiveToOriginal_injective K p)).toEquiv
  change Nat.card (signedFixed K (RingEquiv.refl K) false)=Nat.card (originalFixedPositive K p) at hc
  rw [htop,Subgroup.card_top] at hc
  have hs := fixedPositive_square_lt_original_order K p
  rw [hc] at hs
  have hpos := Nat.card_pos (α:=Projective CartanMatrix.F₄ K)
  nlinarith

end SymmetricSubgroupAsymptotics.CFSGFFourE6FixedPositiveProjection
