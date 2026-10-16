import SymmetricSubgroupAsymptotics.BinaryTwoTernaryAbelianB6Envelope
import SymmetricSubgroupAsymptotics.ScalarFourHeadDefinitions
import Mathlib.GroupTheory.SpecificGroups.Cyclic

/-! When only invariant coordinates remain, the actual kernel is central.
The actual cube map extends both binary kernel coordinates to the whole
target, without a splitting or arbitrary character-extension premise. -/
set_option autoImplicit false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics
namespace CubicZeroScalarKernelEnvelope

variable {Q : Type} [Group Q] [Finite Q]
  (top : Q →* CyclicThree)
  (a : Fin 2 → (top.ker →* Multiplicative (ZMod 2)))
  (hjoint : Function.Injective (fun p : top.ker => (a 0 p,a 1 p)))
  (hfixed : ∀ q p j, a j (MulAut.conjNormal q p) = a j p)
  (hexp : ∀ p : top.ker, p ^ 2 = 1)

include a hjoint hfixed in
omit [Finite Q] in
private theorem kernel_central : top.ker ≤ Subgroup.center Q := by
  intro p hp
  rw [Subgroup.mem_center_iff]
  intro q
  have he : MulAut.conjNormal q (⟨p,hp⟩ : top.ker) = ⟨p,hp⟩ :=
    hjoint (Prod.ext (hfixed q ⟨p,hp⟩ 0) (hfixed q ⟨p,hp⟩ 1))
  have hh := congrArg Subtype.val he
  change q*p*q⁻¹=p at hh
  calc q*p = (q*p*q⁻¹)*q := by group
    _ = p*q := by rw [hh]

private theorem cubic_three_pow : ∀ c : CyclicThree, c ^ 3 = 1 := by decide +kernel

/-- Full-source certificate on this original zero-scalar target. -/
def certificate (hKP : KovacsPraegerAbelianizationBound) :
    PreE7B6QuotientCertificate Q := by
  letI : CommGroup Q := commGroupOfCyclicCenterQuotient top (kernel_central top a hjoint hfixed)
  let cube : Q →* top.ker :=
    { toFun := fun q => ⟨q^3,by
        rw [MonoidHom.mem_ker,map_pow]
        exact cubic_three_pow (top q)⟩
      map_one' := by apply Subtype.ext; simp
      map_mul' := by intro q r; apply Subtype.ext; exact mul_pow q r 3 }
  let b : Fin 2 → (Q →* Multiplicative (ZMod 2)) := fun j => (a j).comp cube
  have hb : Function.Injective (fun q => ((b 0 q,top q),b 1 q)) := by
    intro q r he
    have h0 : a 0 (cube q) = a 0 (cube r) :=
      congrArg (fun z : (Multiplicative (ZMod 2) × CyclicThree) ×
        Multiplicative (ZMod 2) => z.1.1) he
    have h1 : a 1 (cube q) = a 1 (cube r) :=
      congrArg (fun z : (Multiplicative (ZMod 2) × CyclicThree) ×
        Multiplicative (ZMod 2) => z.2) he
    have hc : cube q = cube r := hjoint (Prod.ext h0 h1)
    have hc3 : q^3=r^3 := congrArg Subtype.val hc
    have ht : top q = top r :=
      congrArg (fun z : (Multiplicative (ZMod 2) × CyclicThree) ×
        Multiplicative (ZMod 2) => z.1.2) he
    let d := q⁻¹*r
    have hdK : d ∈ top.ker := by
      rw [MonoidHom.mem_ker,map_mul,map_inv,ht,inv_mul_cancel]
    have hd2 : d^2=1 := congrArg Subtype.val (hexp ⟨d,hdK⟩)
    have hd3 : d^3=1 := by
      dsimp [d]
      rw [mul_pow,inv_pow,hc3,inv_mul_cancel]
    have hd1 : d=1 := by
      calc d = d^2*d := by rw [hd2,one_mul]
        _ = d^3 := (pow_succ d 2).symm
        _ = 1 := hd3
    exact inv_mul_eq_one.mp hd1
  exact BinaryTwoTernaryAbelianB6Envelope.b6Certificate b top hb hKP

end CubicZeroScalarKernelEnvelope
end SymmetricSubgroupAsymptotics
end
