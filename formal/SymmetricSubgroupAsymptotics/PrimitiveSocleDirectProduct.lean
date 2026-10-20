import SymmetricSubgroupAsymptotics.PrimitiveSocleMinimalNormalAlternatives
import Mathlib.GroupTheory.NoncommCoprod
import Mathlib.Logic.Equiv.Fin.Basic

/-! Literal direct-product and homogeneous-coordinate assembly for the
one- and two-minimal-normal alternatives of a primitive action. -/
set_option autoImplicit false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics.PrimitiveSocleONanScottHelpers

/-- Commuting disjoint subgroups form their actual internal direct product. -/
def commutingDisjointSupEquiv {G : Type} [Group G]
    (E C : Subgroup G) (hdis : Disjoint E C)
    (hcomm : ∀ e : E, ∀ c : C, Commute (e : G) (c : G)) :
    E×C ≃* (E⊔C : Subgroup G) := by
  let f : E×C →* G := E.subtype.noncommCoprod C.subtype hcomm
  have hi : Function.Injective f := by
    rw [injective_iff_map_eq_one]
    rintro ⟨e,c⟩ he
    change (e : G)*(c : G)=1 at he
    have hec : (e : G)=(c : G)⁻¹ := mul_eq_one_iff_eq_inv.mp he
    have heone : (e : G)=1 := by
      apply Subgroup.mem_bot.mp
      apply hdis.le_bot
      exact ⟨e.property,by rw [hec]; exact C.inv_mem c.property⟩
    apply Prod.ext
    · exact Subtype.ext heone
    · apply Subtype.ext
      simpa only [heone,one_mul] using he
  have hr : f.range=E⊔C := by
    rw [MonoidHom.noncommCoprod_range,Subgroup.range_subtype,Subgroup.range_subtype]
  exact (MonoidHom.ofInjective hi).trans (MulEquiv.subgroupCongr hr)

private def doubleFunctionEquiv (T : Type) [Group T] (k : ℕ) :
    ((Fin k → T)×(Fin k → T)) ≃* (Fin (k+k) → T) := by
  let e : ((Fin k ⊕ Fin k) → T) ≃* ((Fin k → T)×(Fin k → T)) := {
    toFun := fun f => (fun i => f (.inl i),fun i => f (.inr i))
    invFun := fun f => Sum.elim f.1 f.2
    left_inv := by intro f; funext i; cases i <;> rfl
    right_inv := fun _ => rfl
    map_mul' := fun _ _ => rfl }
  exact e.symm.trans (MulEquiv.arrowCongr finSumFinEquiv (MulEquiv.refl T))

namespace HomogeneousNonabelianChart

variable {E : Type} [Group E] (C : HomogeneousNonabelianChart E)

/-- Transport only the carrier; the same simple group and coordinates remain. -/
def transport {F : Type} [Group F] (e : E ≃* F) : HomogeneousNonabelianChart F where
  Simple := C.Simple
  noncommutative := C.noncommutative
  factorCount := C.factorCount
  factorCount_pos := C.factorCount_pos
  equiv := e.symm.trans C.equiv

/-- The two regular minimal normals have twice the original simple count. -/
def square : HomogeneousNonabelianChart (E×E) where
  Simple := C.Simple
  noncommutative := C.noncommutative
  factorCount := C.factorCount+C.factorCount
  factorCount_pos := by have h := C.factorCount_pos; omega
  equiv := (C.equiv.prodCongr C.equiv).trans
    (doubleFunctionEquiv C.Simple C.factorCount)

/-- Exact cardinality from the actual homogeneous group chart. -/
theorem cardinality : Nat.card E=Nat.card C.Simple ^ C.factorCount := by
  rw [Nat.card_congr C.equiv.toEquiv,Nat.card_fun,Nat.card_fin]

end HomogeneousNonabelianChart
end SymmetricSubgroupAsymptotics.PrimitiveSocleONanScottHelpers
