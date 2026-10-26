import SymmetricSubgroupAsymptotics.DiagonalInvariantSubmodules
import Mathlib.LinearAlgebra.LinearIndependent.Lemmas
import Mathlib.LinearAlgebra.Dimension.Finite
import Mathlib.Data.Finite.Prod

/-! Every actual diagonal character occurring on a full-coordinate
invariant subspace contributes one independent vector. A faithful finite
unit-valued diagonal code therefore has at most |Kˣ|^dim(W) elements.
Equal characters remain one isotype throughout; no multiplicity division,
semisimplicity assumption or code enumeration is used. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics.DiagonalScalarCodeDimensionBound
open DiagonalIsotypeProjection DiagonalInvariantSubmodules

theorem character_card_le_finrank
    {K I J : Type*} [Field K] [Fintype I]
    (scalar : I → J → K) (W : Submodule K (I → K))
    (hstable : ∀ g w,w∈W → diagonalOperator scalar g w∈W)
    (hfull : FullCoordinates W) :
    Nat.card (CharacterLabel scalar)≤Module.finrank K W := by
  let index : CharacterLabel scalar → I := fun χ => Classical.choose χ.property
  have hindex (χ : CharacterLabel scalar) : scalar (index χ)=χ.val :=
    Classical.choose_spec χ.property
  let x : CharacterLabel scalar → W := fun χ => Classical.choose (hfull (index χ) 1)
  have hx (χ : CharacterLabel scalar) : (x χ).val (index χ)=1 :=
    Classical.choose_spec (hfull (index χ) 1)
  let v : CharacterLabel scalar → W := fun χ =>
    ⟨isotypeProjection scalar χ (x χ).val,
      isotypeProjection_mem scalar W hstable χ (x χ).val (x χ).property⟩
  let f : CharacterLabel scalar → Module.Dual K W := fun χ => {
    toFun := fun w => w.val (index χ)
    map_add' := fun _ _ => rfl
    map_smul' := fun _ _ => rfl }
  have hzero : Pairwise (fun χ ψ => f χ (v ψ)=0) := by
    intro χ ψ hne
    have hi : scalar (index χ)≠ψ.val := by
      intro he
      exact hne (Subtype.ext ((hindex χ).symm.trans he))
    change isotypeProjection scalar ψ (x ψ).val (index χ)=0
    rw [isotypeProjection_apply,if_neg hi]
  have hone (χ : CharacterLabel scalar) : f χ (v χ)=1 := by
    change isotypeProjection scalar χ (x χ).val (index χ)=1
    rw [isotypeProjection_apply,if_pos (hindex χ)]
    exact hx χ
  have hlin : LinearIndependent K v :=
    LinearIndependent.of_pairwise_dual_eq_zero_one v f hzero hone
  simpa only [Nat.card_eq_fintype_card] using hlin.fintype_card_le_finrank

theorem code_card_le_units_pow_finrank
    {K I E : Type*} [Field K] [Finite K] [Fintype I] [Finite E]
    (a : E → I → Kˣ) (ha : Function.Injective a)
    (W : Submodule K (I → K))
    (hstable : ∀ g w,w∈W → (fun i => (a g i : K)*w i)∈W)
    (hfull : FullCoordinates W) :
    Nat.card E≤Nat.card Kˣ ^ Module.finrank K W := by
  letI : Finite Kˣ := Finite.of_injective (fun u : Kˣ => (u : K)) Units.val_injective
  let scalar : I → E → K := fun i g => (a g i : K)
  let index : CharacterLabel scalar → I := fun χ => Classical.choose χ.property
  have hindex (χ : CharacterLabel scalar) : scalar (index χ)=χ.val :=
    Classical.choose_spec χ.property
  let code : E → (CharacterLabel scalar → Kˣ) := fun g χ => a g (index χ)
  have hcode : Function.Injective code := by
    intro g h he
    apply ha
    funext i
    let χ : CharacterLabel scalar := coordinateLabel scalar i
    have hg : (a g (index χ) : K)=(a g i : K) := congrFun (hindex χ) g
    have hh : (a h (index χ) : K)=(a h i : K) := congrFun (hindex χ) h
    apply Units.ext
    exact hg.symm.trans ((congrArg (fun u : Kˣ => (u : K)) (congrFun he χ)).trans hh)
  have hdim : Nat.card (CharacterLabel scalar)≤Module.finrank K W :=
    character_card_le_finrank scalar W hstable hfull
  calc
    _≤Nat.card (CharacterLabel scalar → Kˣ) := Nat.card_le_card_of_injective code hcode
    _=Nat.card Kˣ ^ Nat.card (CharacterLabel scalar) := Nat.card_fun
    _≤Nat.card Kˣ ^ Module.finrank K W :=
      Nat.pow_le_pow_right (Nat.card_pos (α:=Kˣ)) hdim

end SymmetricSubgroupAsymptotics.DiagonalScalarCodeDimensionBound
