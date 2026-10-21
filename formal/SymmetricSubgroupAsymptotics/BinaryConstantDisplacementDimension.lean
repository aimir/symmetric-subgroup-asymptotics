import SymmetricSubgroupAsymptotics.BinaryPointSeparatingConstantDisplacements
import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.LinearAlgebra.Dimension.Finite
import Mathlib.Algebra.Module.ZMod
import Mathlib.Algebra.Field.ZMod
import Mathlib.FieldTheory.Finiteness
import Mathlib.SetTheory.Cardinal.Finite
import Mathlib.Tactic.LinearCombination

/-! Constant-displacement functions on a transitive sixteen-point action
form a space of dimension at most four unless squares fix every original
point. Evaluation differences form an actual affine translation orbit;
no permutation catalogue or group-order hypothesis is used. -/
set_option autoImplicit false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics.BinaryConstantDisplacementDimension
local instance constantDisplacementPrimeTwo : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
variable {G X : Type} [Group G] [MulAction G X] [Finite X]
    [MulAction.IsPretransitive G X]
abbrev Bit := ZMod 2

def pointEval (W : Submodule Bit (X → Bit)) (x : X) : Module.Dual Bit W where
  toFun v := v.val x
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

def pointDifference (W : Submodule Bit (X → Bit)) (x₀ x : X) : Module.Dual Bit W :=
  pointEval W x-pointEval W x₀

def differenceGroup (W : Submodule Bit (X → Bit)) (x₀ : X)
    (hconstant : ∀ (g : G) (v : W) (x y : X),
      v.val (g • x)-v.val x=v.val (g • y)-v.val y) :
    AddSubgroup (Module.Dual Bit W) where
  carrier := Set.range (pointDifference W x₀)
  zero_mem' := ⟨x₀,by ext v;simp [pointDifference]⟩
  add_mem' := by
    rintro _ _ ⟨x,rfl⟩ ⟨y,rfl⟩
    obtain ⟨g,hg⟩ := MulAction.exists_smul_eq G x₀ x
    refine ⟨g • y,?_⟩
    ext v
    change v.val (g • y)-v.val x₀=
      (v.val x-v.val x₀)+(v.val y-v.val x₀)
    have h := hconstant g v y x₀
    rw [hg] at h
    linear_combination h
  neg_mem' := by
    rintro _ ⟨x,rfl⟩
    refine ⟨x,?_⟩
    ext v
    exact (CharTwo.neg_eq ((pointDifference W x₀ x) v)).symm

theorem finrank_le_four_of_not_squares_trivial
    (W : Submodule Bit (X → Bit)) (x₀ : X) (hdegree : Nat.card X=16)
    (hconstant : ∀ (g : G) (v : W) (x y : X),
      v.val (g • x)-v.val x=v.val (g • y)-v.val y)
    (hnon : ¬BinarySquareActionStructure.SquaresActTrivially (G := G) (X := X)) :
    Module.finrank Bit W≤4 := by
  let D : Submodule Bit (Module.Dual Bit W) :=
    AddSubgroup.toZModSubmodule 2 (differenceGroup W x₀ hconstant)
  let point : X → D := fun x => ⟨pointDifference W x₀ x,⟨x,rfl⟩⟩
  have hpoint : Function.Surjective point := by
    rintro ⟨d,x,rfl⟩
    exact ⟨x,rfl⟩
  letI : Finite D := Finite.of_surjective point hpoint
  letI : Finite (Module.Dual Bit D) := Finite.of_injective
    (fun f : Module.Dual Bit D => (f : D → Bit)) DFunLike.coe_injective
  have hD : Nat.card D≤16 :=
    (Nat.card_le_card_of_surjective point hpoint).trans_eq hdegree
  let f : W →ₗ[Bit] Bit × Module.Dual Bit D :=
    (pointEval W x₀).prod (D.subtype.dualMap.comp (Module.Dual.eval Bit W))
  have hf : Function.Injective f := by
    intro v w he
    have h₀ := congrArg Prod.fst he
    change v.val x₀=w.val x₀ at h₀
    apply Subtype.ext
    funext x
    have hx := congrArg (fun y : Bit × Module.Dual Bit D => y.2 (point x)) he
    change v.val x-v.val x₀=w.val x-w.val x₀ at hx
    linear_combination hx+h₀
  have hdual : Nat.card (Module.Dual Bit D)=Nat.card D := by
    rw [Module.natCard_eq_pow_finrank (K := Bit) (V := Module.Dual Bit D),
      Module.natCard_eq_pow_finrank (K := Bit) (V := D),Subspace.dual_finrank_eq]
  have hW := Nat.card_le_card_of_injective f hf
  rw [Nat.card_prod,hdual] at hW
  norm_num only [Bit,Nat.card_zmod] at hW
  by_contra hbad
  have hlarge : 32≤Nat.card W := by
    rw [Module.natCard_eq_pow_finrank (K := Bit)]
    norm_num only [Bit,Nat.card_zmod]
    change 2^5≤2^Module.finrank Bit W
    exact Nat.pow_le_pow_right (by decide : 0<(2 : ℕ)) (by omega)
  have hcard : Nat.card X=Nat.card D := by omega
  have hpointinj : Function.Injective point :=
    ((Nat.bijective_iff_surjective_and_card point).mpr ⟨hpoint,hcard⟩).injective
  have hseparate : Function.Injective (fun x : X => fun v : W => v.val x) := by
    intro x y hxy
    apply hpointinj
    apply Subtype.ext
    apply LinearMap.ext
    intro v
    change v.val x-v.val x₀=v.val y-v.val x₀
    have hv : v.val x=v.val y := congrFun hxy v
    rw [hv]
  apply hnon
  exact squaresActTrivially_of_pointSeparating_constant_displacements
    (fun v : W => v.val) hseparate (fun g v x y => hconstant g v x y)

end SymmetricSubgroupAsymptotics.BinaryConstantDisplacementDimension
