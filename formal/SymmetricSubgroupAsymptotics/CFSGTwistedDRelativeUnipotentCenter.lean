import SymmetricSubgroupAsymptotics.CFSGTwistedDRelativeHighestRoot

/-! The centre of the actual relative defining-characteristic Sylow is
the additive group of the literal fixed field. No polar reconstruction
or automorphism-counting statement is assumed here. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGTwistedDRelativeUnipotentCenter
open CFSGOrthogonalDSerreMatrices CFSGTwistedDRelativeUnipotentSylow
open CFSGTwistedDRelativeHighestRoot CFSGTwistedA2FixedField
open CFSGOrthogonalDIndexFlagVectors CFSGOrthogonalDGenerationRootArrays
open CFSGOrthogonalDIndexHighestRoot CFSGOrthogonalDIndexUnipotentCenter

theorem highest_injective (s : ℕ) (q : CFSG.PrimePower) :
    Function.Injective (highestInRelativeU s q) := by
  intro a b h
  apply Subtype.ext
  have he := congrArg (fun u : unipotent s q =>
    (u.val.val : Mat (q.Extension 2) (s + 4)) (Sum.inl 0) (Sum.inr (secondIndex s))) h
  dsimp only at he
  rw [highestInRelativeU_val, highestInRelativeU_val] at he
  simpa [plusArray, Matrix.one_apply, Matrix.single_apply,
    zero_ne_second, Ne.symm (zero_ne_second s)] using he

theorem highest_zero (s : ℕ) (q : CFSG.PrimePower) : highestInRelativeU s q 0 = 1 := by
  apply Subtype.ext
  apply Subtype.ext
  exact congrArg
    (fun u : CFSGOrthogonalDIndexUnipotent.unipotent (q.Extension 2) (s + 4) => u.val.val)
    (highestInU_zero (q.Extension 2) s)

theorem highest_add (s : ℕ) (q : CFSG.PrimePower) (a b : fixedField q) :
    highestInRelativeU s q (a + b) = highestInRelativeU s q a * highestInRelativeU s q b := by
  apply Subtype.ext
  apply Subtype.ext
  exact congrArg
    (fun u : CFSGOrthogonalDIndexUnipotent.unipotent (q.Extension 2) (s + 4) => u.val.val)
    (highestInU_add (q.Extension 2) s (a : q.Extension 2) (b : q.Extension 2))

def highestHom (s : ℕ) (q : CFSG.PrimePower) :
    Multiplicative (fixedField q) →* unipotent s q where
  toFun a := highestInRelativeU s q a.toAdd
  map_one' := highest_zero s q
  map_mul' a b := highest_add s q a.toAdd b.toAdd

def highestCenterHom (s : ℕ) (q : CFSG.PrimePower) :
    Multiplicative (fixedField q) →* Subgroup.center (unipotent s q) :=
  (highestHom s q).codRestrict _ (fun a => highestInRelativeU_mem_center s q a.toAdd)

def centerFieldEquiv (s : ℕ) (q : CFSG.PrimePower) :
    Multiplicative (fixedField q) ≃* Subgroup.center (unipotent s q) :=
  MulEquiv.ofBijective (highestCenterHom s q) ⟨by
    intro a b h
    have he := highest_injective s q (congrArg Subtype.val h)
    exact congrArg Multiplicative.ofAdd he, by
    intro z
    obtain ⟨a, ha⟩ := center_eq_highest s q z.val z.property
    refine ⟨Multiplicative.ofAdd a, ?_⟩
    apply Subtype.ext
    exact ha.symm⟩

theorem center_card (s : ℕ) (q : CFSG.PrimePower) :
    Nat.card (Subgroup.center (unipotent s q)) = q.order := by
  calc
    Nat.card (Subgroup.center (unipotent s q)) = Nat.card (Multiplicative (fixedField q)) :=
      Nat.card_congr (centerFieldEquiv s q).symm.toEquiv
    _ = Nat.card (fixedField q) := Nat.card_congr Multiplicative.toAdd
    _ = q.order := fixedField_card q

end SymmetricSubgroupAsymptotics.CFSGTwistedDRelativeUnipotentCenter
