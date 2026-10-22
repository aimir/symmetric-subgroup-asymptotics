import SymmetricSubgroupAsymptotics.CFSGOrthogonalDIndexTailOperators
import SymmetricSubgroupAsymptotics.CFSGOrthogonalDBinaryElements

/-! The actual D tail root group embeds in the next original D group,
for the genuine rank guard n>=2. Every original root word is sent to
its actual successor-index root; membership follows from the defining
closure, not from an abstract low-rank identification. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGOrthogonalDIndexTailCoordinates
open CFSGOrthogonalDSerreMatrices
variable (K : Type) [Field K]

theorem tailUnitHom_rootTransvection (n : ℕ) (hn : 2 ≤ n) (neg : Bool) (i : Fin n) (a : K) :
    tailUnitHom K n (rootTransvection K n neg i a) = rootTransvection K (n + 1) neg i.succ a := by
  apply Units.ext
  change tailMatrixHom K n (rootTransvection K n neg i a : Mat K n) =
    (rootTransvection K (n + 1) neg i.succ a : Mat K (n + 1))
  rw [tailMatrixHom_eq_one_add, rootTransvection_val, rootTransvection_val,
    add_sub_cancel_left, map_smul, zeroTailLinear_rootMatrix K n hn neg i]

theorem tailUnitHom_maps_elementary (n : ℕ) (hn : 2 ≤ n) :
    elementaryRootGroup K n ≤ (elementaryRootGroup K (n + 1)).comap (tailUnitHom K n) := by
  apply (Subgroup.closure_le _).mpr
  rintro g ⟨neg, i, a, rfl⟩
  change tailUnitHom K n (rootTransvection K n neg i a) ∈ elementaryRootGroup K (n + 1)
  rw [tailUnitHom_rootTransvection K n hn]
  exact rootTransvection_mem K (n + 1) neg i.succ a

def tailElementaryHom (n : ℕ) (hn : 2 ≤ n) :
    elementaryRootGroup K n →* elementaryRootGroup K (n + 1) where
  toFun g := ⟨tailUnitHom K n g.val, tailUnitHom_maps_elementary K n hn g.property⟩
  map_one' := Subtype.ext ((tailUnitHom K n).map_one)
  map_mul' g h := Subtype.ext ((tailUnitHom K n).map_mul g.val h.val)

theorem tailElementaryHom_injective (n : ℕ) (hn : 2 ≤ n) :
    Function.Injective (tailElementaryHom K n hn) := by
  intro g h he
  apply Subtype.ext
  apply tailUnitHom_injective K n
  exact congrArg Subtype.val he

theorem tailElementaryHom_rootElement (n : ℕ) (hn : 2 ≤ n)
    (neg : Bool) (i : Fin n) (a : K) :
    tailElementaryHom K n hn (CFSGOrthogonalDBinaryElements.rootElement K n neg i a) =
      CFSGOrthogonalDBinaryElements.rootElement K (n + 1) neg i.succ a :=
  Subtype.ext (tailUnitHom_rootTransvection K n hn neg i a)

end SymmetricSubgroupAsymptotics.CFSGOrthogonalDIndexTailCoordinates
