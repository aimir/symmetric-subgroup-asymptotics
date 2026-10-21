import SymmetricSubgroupAsymptotics.BinaryElementary32CoordinateRows
import SymmetricSubgroupAsymptotics.BinaryFiveHyperplaneCover

/-! Four literal original generators bound fixed vectors, while all sixteen
literal original word rows bound the top factor. The two factors use the
same displacement subspace and the exact eleven-dimensional kernel. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics.BinaryElementary32FiniteCapacity
local instance elementaryFiniteCapacityFactPrimeTwo : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
open BinaryElementary16GraphHeadRigidity
abbrev K := stateChart 0

abbrev fixedVectors (A : Submodule (ZMod 2) V) :=
  {v : V // v∈K.space ∧ ∀ i : Fin 4,action i v-v∈A}

def allowedWords (A : Submodule (ZMod 2) V) : Finset (Fin 16) := Finset.univ.filter fun i =>
  ∀ j : Fin 11,BinaryElementary32DerivedHyperplaneOne.rowAction i (K.inclusion (Pi.single j 1))-
    K.inclusion (Pi.single j 1)∈A

def capacity (A : Submodule (ZMod 2) V) : ℕ :=
  Nat.card (fixedVectors A)*(allowedWords A).card

theorem capacity_mono (A B : Submodule (ZMod 2) V) (hAB : A≤B) : capacity A≤capacity B := by
  let f : fixedVectors A → fixedVectors B :=
    fun v => ⟨v.val,v.property.1,fun i => hAB (v.property.2 i)⟩
  have hf : Function.Injective f := fun _ _ he => Subtype.ext
    (congrArg (fun z : fixedVectors B => z.val) he)
  have ht : allowedWords A⊆allowedWords B := by
    intro i hi
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_univ _,fun j => ?_⟩
    exact hAB ((Finset.mem_filter.mp hi).2 j)
  exact Nat.mul_le_mul (Nat.card_le_card_of_injective f hf) (Finset.card_le_card ht)

theorem original_capacity_le {G : Type} [Group G] [Finite G]
    (rho : Representation (ZMod 2) G V) (u : Fin 4 → G)
    (hu : ∀ i,rho (u i)=action i)
    (hb : Function.Bijective (BinaryElementary32CoordinateRows.word u))
    (A : Submodule (ZMod 2) V) :
    binaryJointDisplacementCapacity rho K.space A≤capacity A := by
  let e : Fin 16 ≃ G := Equiv.ofBijective (BinaryElementary32CoordinateRows.word u) hb
  let f : binaryFixedDisplacements rho K.space A → fixedVectors A := fun v =>
    ⟨v.val,v.property.1,fun i => by rw [←hu];exact v.property.2 (u i)⟩
  have hf : Function.Injective f := fun _ _ he => Subtype.ext
    (congrArg (fun z : fixedVectors A => z.val) he)
  let t : binaryTrivialDisplacements rho K.space A → allowedWords A := fun g =>
    ⟨e.symm g.val,by
      apply Finset.mem_filter.mpr
      refine ⟨Finset.mem_univ _,fun j => ?_⟩
      rw [←BinaryElementary32CoordinateRows.word_action rho u hu]
      have he : BinaryElementary32CoordinateRows.word u (e.symm g.val)=g.val := e.apply_symm_apply g.val
      rw [he]
      exact g.property _ ⟨Pi.single j 1,rfl⟩⟩
  have ht : Function.Injective t := by
    intro g h he
    apply Subtype.ext
    exact e.symm.injective (congrArg (fun z : allowedWords A => z.val) he)
  have hc := Nat.card_le_card_of_injective t ht
  have hc' : Nat.card (binaryTrivialDisplacements rho K.space A)≤(allowedWords A).card := by
    exact hc.trans_eq (by simp only [Nat.card_eq_fintype_card,Fintype.card_coe])
  exact Nat.mul_le_mul (Nat.card_le_card_of_injective f hf) hc'

/-- The selected lower-layer pilot already bounds every smaller actual
axis. This is the pilot result consumed by the coordinate installer. -/
theorem lowerLayer_capacity_le : capacity BinaryElementary32DerivedHyperplaneOne.lowerLayer≤512 := by
  letI : Finite BinaryElementary32DerivedHyperplaneOne.FixedVectors := by
    unfold BinaryElementary32DerivedHyperplaneOne.FixedVectors
    infer_instance
  let f : fixedVectors BinaryElementary32DerivedHyperplaneOne.lowerLayer →
      BinaryElementary32DerivedHyperplaneOne.FixedVectors := fun v =>
    ⟨v.val,v.property.1,fun i => v.property.2 i⟩
  have hf : Function.Injective f := fun _ _ he => Subtype.ext
    (congrArg (fun z : BinaryElementary32DerivedHyperplaneOne.FixedVectors => z.val) he)
  have hc : Nat.card (fixedVectors BinaryElementary32DerivedHyperplaneOne.lowerLayer)≤256 :=
    (Nat.card_le_card_of_injective f hf).trans BinaryElementary32DerivedHyperplaneOne.fixed_card_le
  have hs : allowedWords BinaryElementary32DerivedHyperplaneOne.lowerLayer⊆
      BinaryElementary32DerivedHyperplaneOne.allowedTop := by
    intro i hi
    apply Finset.mem_filter.mpr
    exact ⟨Finset.mem_univ _,(Finset.mem_filter.mp hi).2⟩
  have ht : (allowedWords BinaryElementary32DerivedHyperplaneOne.lowerLayer).card≤2 :=
    (Finset.card_le_card hs).trans_eq BinaryElementary32DerivedHyperplaneOne.allowedTop_card
  exact (Nat.mul_le_mul hc ht).trans (by norm_num)

end SymmetricSubgroupAsymptotics.BinaryElementary32FiniteCapacity
