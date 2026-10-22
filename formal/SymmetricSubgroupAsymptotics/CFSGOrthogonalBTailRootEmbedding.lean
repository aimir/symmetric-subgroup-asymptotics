import SymmetricSubgroupAsymptotics.CFSGOrthogonalBTailOperators
import SymmetricSubgroupAsymptotics.CFSGOrthogonalBGenerationElements

/-! The actual B tail root group embeds in the next original B group.
Every original root word is carried to its actual successor-index root
word; membership of the full group follows from the original closure. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGOrthogonalBTailCoordinates
open CFSGOrthogonalBSerreMatrices CFSGOrthogonalBGenerationElements
variable (K : Type) [Field K]

theorem zeroTailLinear_rootMatrix (n : ℕ) (neg : Bool) (i : Fin n) :
    zeroTailLinear K n (rootMatrix K n neg i) = rootMatrix K (n + 1) neg i.succ := by
  cases neg
  · simpa only [rootMatrix, Bool.false_eq_true, if_false] using zeroTailLinear_positive K n i
  · simpa only [rootMatrix, if_true] using zeroTailLinear_negative K n i

theorem zeroTailLinear_rootSecond (n : ℕ) (neg : Bool) (i : Fin n) :
    zeroTailLinear K n (rootSecond K n neg i) = rootSecond K (n + 1) neg i.succ := by
  cases neg
  · simpa only [rootSecond, Bool.false_eq_true, if_false] using zeroTailLinear_positiveSecond K n i
  · simpa only [rootSecond, if_true] using zeroTailLinear_negativeSecond K n i

theorem tailUnitHom_rootTransvection (n : ℕ) (neg : Bool) (i : Fin n) (a : K) :
    tailUnitHom K n (rootTransvection K n neg i a) = rootTransvection K (n + 1) neg i.succ a := by
  apply Units.ext
  change tailMatrixHom K n (rootTransvection K n neg i a : Mat K n) =
    (rootTransvection K (n + 1) neg i.succ a : Mat K (n + 1))
  rw [tailMatrixHom_eq_one_add, rootTransvection_val, rootTransvection_val]
  have hp : (1 + a • rootMatrix K n neg i + a ^ 2 • rootSecond K n neg i) - 1 =
      a • rootMatrix K n neg i + a ^ 2 • rootSecond K n neg i := by abel
  rw [hp, map_add, map_smul, map_smul, zeroTailLinear_rootMatrix, zeroTailLinear_rootSecond]
  abel

theorem tailUnitHom_maps_elementary (n : ℕ) :
    elementaryRootGroup K n ≤ (elementaryRootGroup K (n + 1)).comap (tailUnitHom K n) := by
  apply (Subgroup.closure_le _).mpr
  rintro g ⟨neg, i, a, rfl⟩
  change tailUnitHom K n (rootTransvection K n neg i a) ∈ elementaryRootGroup K (n + 1)
  rw [tailUnitHom_rootTransvection]
  exact rootTransvection_mem K (n + 1) neg i.succ a

def tailElementaryHom (n : ℕ) : elementaryRootGroup K n →* elementaryRootGroup K (n + 1) where
  toFun g := ⟨tailUnitHom K n g.val, tailUnitHom_maps_elementary K n g.property⟩
  map_one' := Subtype.ext ((tailUnitHom K n).map_one)
  map_mul' g h := Subtype.ext ((tailUnitHom K n).map_mul g.val h.val)

theorem tailElementaryHom_injective (n : ℕ) : Function.Injective (tailElementaryHom K n) := by
  intro g h he
  apply Subtype.ext
  apply tailUnitHom_injective K n
  exact congrArg Subtype.val he

theorem tailElementaryHom_rootElement (n : ℕ) (neg : Bool) (i : Fin n) (a : K) :
    tailElementaryHom K n (rootElement K n neg i a) = rootElement K (n + 1) neg i.succ a :=
  Subtype.ext (tailUnitHom_rootTransvection K n neg i a)

end SymmetricSubgroupAsymptotics.CFSGOrthogonalBTailCoordinates
