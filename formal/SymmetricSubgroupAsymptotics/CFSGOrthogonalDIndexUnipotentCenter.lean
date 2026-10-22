import SymmetricSubgroupAsymptotics.CFSGOrthogonalDIndexHighestRoot

/-! The exact original centre of D flag-unipotent U is the additive
field, through its literal highest-root matrices. This supplies the
actual field layer for later automorphism restriction; it makes no
Sylow or global automorphism-recognition assertion. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGOrthogonalDIndexUnipotentCenter
open CFSGOrthogonalDSerreMatrices CFSGOrthogonalDIndexUnipotent
open CFSGOrthogonalDIndexHighestRoot CFSGOrthogonalDIndexFlagVectors
open CFSGOrthogonalDGenerationRootArrays CFSGMatrixShearUnits
variable (K : Type) [Field K]

theorem highestInU_injective (s : ℕ) : Function.Injective (highestInU K s) := by
  intro a b h
  have he := congrArg (fun u : unipotent K (s + 4) =>
    (u.val.val : Mat K (s + 4)) (Sum.inl 0) (Sum.inr (secondIndex s))) h
  dsimp only at he
  rw [highestInU_val_plus, highestInU_val_plus] at he
  simpa [plusArray, Matrix.one_apply, Matrix.single_apply,
    zero_ne_second, Ne.symm (zero_ne_second s)] using he

theorem highestInU_zero (s : ℕ) : highestInU K s 0 = 1 := by
  apply Subtype.ext
  apply Subtype.ext
  apply Units.ext
  rw [highestInU_val]
  simp

theorem highestInU_add (s : ℕ) (a b : K) :
    highestInU K s (a + b) = highestInU K s a * highestInU K s b := by
  apply Subtype.ext
  apply Subtype.ext
  change CFSGMatrixShearUnits.upper
      (Matrix.single (0 : Fin (s + 4)) (secondIndex s) (a + b) -
        Matrix.single (secondIndex s) 0 (a + b)) =
    CFSGMatrixShearUnits.upper (Matrix.single (0 : Fin (s + 4)) (secondIndex s) a -
      Matrix.single (secondIndex s) 0 a) *
    CFSGMatrixShearUnits.upper (Matrix.single (0 : Fin (s + 4)) (secondIndex s) b -
      Matrix.single (secondIndex s) 0 b)
  rw [← upper_add]
  congr 1
  ext i j
  simp only [Matrix.add_apply, Matrix.sub_apply, Matrix.single_apply]
  split_ifs <;> ring

def highestHom (s : ℕ) : Multiplicative K →* unipotent K (s + 4) where
  toFun a := highestInU K s a.toAdd
  map_one' := highestInU_zero K s
  map_mul' a b := highestInU_add K s a.toAdd b.toAdd

def highestCenterHom (s : ℕ) : Multiplicative K →* Subgroup.center (unipotent K (s + 4)) :=
  (highestHom K s).codRestrict _ (fun a => highestInU_mem_center K s a.toAdd)

def centerFieldEquiv (s : ℕ) : Multiplicative K ≃* Subgroup.center (unipotent K (s + 4)) :=
  MulEquiv.ofBijective (highestCenterHom K s) ⟨by
    intro a b h
    have he := highestInU_injective K s (congrArg Subtype.val h)
    exact congrArg Multiplicative.ofAdd he, by
    intro z
    obtain ⟨a, ha⟩ := center_eq_highestInU K s z.val z.property
    refine ⟨Multiplicative.ofAdd a, ?_⟩
    apply Subtype.ext
    exact ha.symm⟩

theorem center_card (s : ℕ) : Nat.card (Subgroup.center (unipotent K (s + 4))) = Nat.card K := by
  calc
    Nat.card (Subgroup.center (unipotent K (s + 4))) = Nat.card (Multiplicative K) :=
      Nat.card_congr (centerFieldEquiv K s).symm.toEquiv
    _ = Nat.card K := Nat.card_congr Multiplicative.toAdd

end SymmetricSubgroupAsymptotics.CFSGOrthogonalDIndexUnipotentCenter
