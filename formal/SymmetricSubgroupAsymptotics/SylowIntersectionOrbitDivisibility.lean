import SymmetricSubgroupAsymptotics.SylowSubgroupLocalContainment
import Mathlib.GroupTheory.Index

/-! In a transitive action with an actual Sylow-fixed point, a nonfixed
Sylow orbit has stabilizer inside a proper conjugate-Sylow intersection.
Thus any common divisor of those proper relative indices divides every
nonfixed orbit. All stabilizers and the local Sylow witness are actual. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.SylowIntersectionOrbitDivisibility
open MulAction
variable {G X : Type*} [Group G] [Finite G] [MulAction G X]
    [IsPretransitive G X] (p : ℕ) [Fact p.Prime]

theorem dvd_stabilizer_index_of_not_fixed
    (P : Sylow p G) (q : ℕ)
    (hintersection : ∀ g : G,
      (P : Subgroup G) ⊓ ((g • P : Sylow p G) : Subgroup G) ≠ (P : Subgroup G) →
      q ∣ ((P : Subgroup G) ⊓ ((g • P : Sylow p G) : Subgroup G)).relIndex (P : Subgroup G))
    (x : X) (hx : x∈fixedPoints P X) (y : X) (hy : y∉fixedPoints P X) :
    q ∣ (stabilizer P y).index := by
  classical
  obtain ⟨g,hg⟩ := exists_smul_eq G x y
  let K := stabilizer G y
  have hPy : ((g • P : Sylow p G) : Subgroup G)≤K := by
    rintro _ ⟨a,ha,rfl⟩
    change (g*a*g⁻¹) • y=y
    rw [←hg]
    simp only [mul_smul,inv_smul_smul]
    have hax : a • x=x := (mem_fixedPoints.mp hx) ⟨a,ha⟩
    rw [hax]
  let Q : Subgroup P := stabilizer P y
  let R : Subgroup G := Q.map (P : Subgroup G).subtype
  have hRp : IsPGroup p R := (P.2.to_subgroup Q).map (P : Subgroup G).subtype
  have hRK : R≤K := by
    rintro _ ⟨a,ha,rfl⟩
    exact ha
  obtain ⟨h,hh⟩ := SylowSubgroupLocalContainment.exists_conjugate_containing
    p (g • P) K hPy R hRp hRK
  let c := h.val*g
  have hC : ((c • P : Sylow p G) : Subgroup G)≤K := by
    simpa only [c,mul_smul] using Sylow.smul_le hPy h
  have hRC : R≤((c • P : Sylow p G) : Subgroup G) := by
    simpa only [c,mul_smul] using hh
  let I : Subgroup G := (P : Subgroup G) ⊓ ((c • P : Sylow p G) : Subgroup G)
  have hRP : R≤(P : Subgroup G) := by
    rintro _ ⟨a,ha,rfl⟩
    exact a.property
  have hRI : R≤I := le_inf hRP hRC
  have hI : I≠(P : Subgroup G) := by
    intro he
    apply hy
    apply mem_fixedPoints.mpr
    intro a
    have hPI : (P : Subgroup G)≤I := le_of_eq he.symm
    exact hC ((show I≤((c • P : Sylow p G) : Subgroup G) from inf_le_right)
      (hPI a.property))
  have hQI : Q≤I.subgroupOf (P : Subgroup G) := by
    intro a ha
    exact hRI ⟨a,ha,rfl⟩
  have hdiv : q ∣ (I.subgroupOf (P : Subgroup G)).index := hintersection c hI
  exact hdiv.trans (Subgroup.index_dvd_of_le hQI)

theorem dvd_orbit_card_of_not_fixed [Finite X]
    (P : Sylow p G) (q : ℕ)
    (hintersection : ∀ g : G,
      (P : Subgroup G) ⊓ ((g • P : Sylow p G) : Subgroup G) ≠ (P : Subgroup G) →
      q ∣ ((P : Subgroup G) ⊓ ((g • P : Sylow p G) : Subgroup G)).relIndex (P : Subgroup G))
    (x : X) (hx : x∈fixedPoints P X) (y : X) (hy : y∉fixedPoints P X) :
    q ∣ Nat.card (orbit P y) := by
  simpa only [MulAction.index_stabilizer] using
    dvd_stabilizer_index_of_not_fixed p P q hintersection x hx y hy

end SymmetricSubgroupAsymptotics.SylowIntersectionOrbitDivisibility
