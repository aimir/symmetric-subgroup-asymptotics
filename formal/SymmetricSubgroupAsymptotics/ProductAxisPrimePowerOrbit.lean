import SymmetricSubgroupAsymptotics.ProductAxisPGroupOrbit
import SymmetricSubgroupAsymptotics.SylowPrimePowerTransitive

/-! Prime-power coordinate orbits force prime-power whole orbits even
when the actual point stabilizer correlates all factors. -/
set_option autoImplicit false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics.ProductAxisPrimePowerOrbit
variable {J T X : Type} [Group T] [Finite T] [Fintype J] [DecidableEq J]
  [Finite X] [MulAction (J → T) X]

def axisAction (i : J) : MulAction T X :=
  MulAction.compHom X (MonoidHom.mulSingle (fun _ : J => T) i)

theorem card_orbit_prime_power (p : ℕ) [Fact p.Prime]
    (haxis : ∀ (i : J) (x : X),
      letI : MulAction T X := axisAction i
      ∃ r : ℕ,Nat.card (MulAction.orbit T x)=p^r)
    (x₀ : X) : ∃ r : ℕ,Nat.card (MulAction.orbit (J → T) x₀)=p^r := by
  let P : Sylow p T := Classical.choice inferInstance
  let H : J → Subgroup T := fun _ => P
  have hH (i : J) : IsPGroup p (H i) := P.isPGroup'
  have hloc (i : J) (g : T) (x : X) : ∃ h : H i,
      (Pi.mulSingle i h.val : J → T) • x=(Pi.mulSingle i g : J → T) • x := by
    letI : MulAction T X := axisAction i
    obtain ⟨r,hr⟩ := haxis i x
    let x' : MulAction.orbit T x := ⟨x,MulAction.mem_orbit_self x⟩
    let y' : MulAction.orbit T x := ⟨g • x,MulAction.mem_orbit x g⟩
    letI : Nonempty (MulAction.orbit T x) := ⟨x'⟩
    letI : MulAction.IsPretransitive T (MulAction.orbit T x) := ⟨by
      intro y z
      obtain ⟨a,ha⟩ := MulAction.mem_orbit_iff.mp y.property
      obtain ⟨b,hb⟩ := MulAction.mem_orbit_iff.mp z.property
      refine ⟨b*a⁻¹,Subtype.ext ?_⟩
      change (b*a⁻¹) • y.val=z.val
      rw [←ha,mul_smul,inv_smul_smul,hb]⟩
    letI : MulAction.IsPretransitive P (MulAction.orbit T x) :=
      sylow_isPretransitive_of_card_eq_prime_pow P hr
    obtain ⟨h,hh⟩ := MulAction.exists_smul_eq P x' y'
    have he := congrArg Subtype.val hh
    change (Pi.mulSingle i h.val : J → T) • x=(Pi.mulSingle i g : J → T) • x at he
    exact ⟨h,he⟩
  exact ProductAxisPGroupOrbit.card_orbit_prime_power H hH hloc x₀

end SymmetricSubgroupAsymptotics.ProductAxisPrimePowerOrbit
