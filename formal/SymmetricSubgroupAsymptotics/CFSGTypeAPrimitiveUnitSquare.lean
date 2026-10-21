import SymmetricSubgroupAsymptotics.CFSGTypeAFiniteFieldScalars
import Lean.Elab.Tactic.Omega

/-! The only scalar exclusion used in the actual torus/Weyl generating
pair. It follows from the order of the finite field's unit group. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGTypeAPrimitiveUnitSquare
variable {F : Type*} [Field F] [Finite F]

theorem square_ne_one (hcard : 4≤Nat.card F) (g : Fˣ)
    (hg : ∀ u : Fˣ,u∈Subgroup.zpowers g) : (g : F)^2≠1 := by
  intro h
  have hu : g^2=1 := Units.ext (by simpa using h)
  have hd := orderOf_dvd_of_pow_eq_one hu
  rw [orderOf_eq_card_of_forall_mem_zpowers hg,Nat.card_units] at hd
  have hb := Nat.le_of_dvd (by decide : 0<2) hd
  omega

theorem inverse_square_ne_one (hcard : 4≤Nat.card F) (g : Fˣ)
    (hg : ∀ u : Fˣ,u∈Subgroup.zpowers g) : ((g⁻¹ : Fˣ) : F)^2≠1 := by
  intro h
  apply square_ne_one hcard g hg
  have hi := congrArg (fun a : F => a⁻¹) h
  simpa only [Units.val_inv_eq_inv_val,←inv_pow,inv_inv,inv_one] using hi

end SymmetricSubgroupAsymptotics.CFSGTypeAPrimitiveUnitSquare
