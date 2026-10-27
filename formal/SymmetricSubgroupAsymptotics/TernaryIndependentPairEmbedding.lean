import SymmetricSubgroupAsymptotics.TernaryCubePowerHom
import SymmetricSubgroupAsymptotics.TernaryPairedInversionIndependence
import Mathlib.GroupTheory.NoncommCoprod

/-! A genuine independent C3×C3 from two commuting nontrivial cube-one
elements and one actual endomorphism inverting the first and fixing the
second. This supplies a faithful finite source, not a cardinality premise. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.TernaryIndependentPairEmbedding
open TernaryCubePowerHom
variable {G : Type*} [Group G]
abbrev P := Multiplicative (ZMod 3)

def embedding (u v : G) (hu : u^3=1) (hv : v^3=1) (hc : Commute u v) : P×P →* G :=
  (powerHom u hu).noncommCoprod (powerHom v hv) (by
    intro m n
    change Commute (powerHom u hu (Multiplicative.ofAdd m.toAdd))
      (powerHom v hv (Multiplicative.ofAdd n.toAdd))
    rw [powerHom_val,powerHom_val]
    exact hc.pow_pow _ _)

private theorem value_cube (u : G) (hu : u^3=1) (m : P) : (powerHom u hu m)^3=1 := by
  change (powerHom u hu (Multiplicative.ofAdd m.toAdd))^3=1
  rw [powerHom_val]
  calc
    (u^m.toAdd.val)^3=(u^3)^m.toAdd.val := by
      rw [←pow_mul,←pow_mul,Nat.mul_comm m.toAdd.val 3]
    _=1 := by rw [hu,one_pow]

theorem embedding_injective (u v : G) (hu : u^3=1) (hv : v^3=1)
    (hc : Commute u v) (hun : u≠1) (hvn : v≠1)
    (f : G →* G) (hfu : f u=u⁻¹) (hfv : f v=v) :
    Function.Injective (embedding u v hu hv hc) := by
  apply (embedding u v hu hv hc).ker_eq_bot_iff.mp
  apply le_antisymm _ bot_le
  intro z hz
  change z=1
  have hrel : powerHom u hu z.1*powerHom v hv z.2=1 := hz
  have hfa : f (powerHom u hu z.1)=(powerHom u hu z.1)⁻¹ := by
    change f (powerHom u hu (Multiplicative.ofAdd z.1.toAdd))=
      (powerHom u hu (Multiplicative.ofAdd z.1.toAdd))⁻¹
    rw [powerHom_val,map_pow,hfu,inv_pow]
  have hfc : f (powerHom v hv z.2)=powerHom v hv z.2 := by
    change f (powerHom v hv (Multiplicative.ofAdd z.2.toAdd))=
      powerHom v hv (Multiplicative.ofAdd z.2.toAdd)
    rw [powerHom_val,map_pow,hfv]
  have hv1 : powerHom v hv z.2=1 :=
    TernaryPairedInversionIndependence.third_eq_one f (powerHom u hu z.1) 1
      (powerHom v hv z.2) (Commute.one_right _) hfa (by simp) hfc
      (value_cube v hv z.2) (by simpa only [mul_one] using hrel)
  have hu1 : powerHom u hu z.1=1 := by simpa only [hv1,mul_one] using hrel
  apply Prod.ext
  · apply powerHom_injective u hu hun
    change powerHom u hu z.1=powerHom u hu (1 : P)
    rw [map_one]
    exact hu1
  · apply powerHom_injective v hv hvn
    change powerHom v hv z.2=powerHom v hv (1 : P)
    rw [map_one]
    exact hv1

end SymmetricSubgroupAsymptotics.TernaryIndependentPairEmbedding
