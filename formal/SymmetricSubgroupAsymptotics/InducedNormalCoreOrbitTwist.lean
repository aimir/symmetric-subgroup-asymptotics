import SymmetricSubgroupAsymptotics.InducedOrbitStabilizer
import SymmetricSubgroupAsymptotics.FiniteRepresentationOrbitDuality

/-! Twisting a local fibre across a Mackey representative preserves its
coefficient orbit count under an actual globally normal core subgroup. -/
set_option autoImplicit false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics

variable {k G V : Type} [Field k] [Group G] [AddCommGroup V] [Module k V]

theorem nonzeroOrbitCard_comp_surjective {A B : Type} [Group A] [Group B]
    (rho : Representation k B V) (f : A →* B) (hf : Function.Surjective f) :
    Nat.card (Quotient (representationNonzeroOrbitRel (rho.comp f)))=
      Nat.card (Quotient (representationNonzeroOrbitRel rho)) := by
  apply Nat.card_congr
  apply Quotient.congr (Equiv.refl _)
  intro x y
  change (∃ a : A,rho (f a) x.val=y.val) ↔ ∃ b : B,rho b x.val=y.val
  constructor
  · rintro ⟨a,ha⟩
    exact ⟨f a,ha⟩
  · rintro ⟨b,hb⟩
    obtain ⟨a,rfl⟩ := hf b
    exact ⟨a,hb⟩

variable (H N B : Subgroup G) [B.Normal] (hBH : B≤H) (hBN : B≤N) (x : G)

def inducedNormalCore : Subgroup (inducedOrbitStabilizer H N x) :=
  B.comap (N.subtype.comp (inducedOrbitStabilizer H N x).subtype)

def inducedNormalCoreTwist : inducedNormalCore H N B x →* B.subgroupOf H where
  toFun l := ⟨inducedOrbitTwist H N x l.val,
    (inferInstance : B.Normal).conj_mem _ l.property x⟩
  map_one' := by
    apply Subtype.ext
    exact map_one (inducedOrbitTwist H N x)
  map_mul' a b := by
    apply Subtype.ext
    exact map_mul (inducedOrbitTwist H N x) a.val b.val

include hBN in
theorem inducedNormalCoreTwist_surjective :
    Function.Surjective (inducedNormalCoreTwist H N B x) := by
  intro b
  let a : G := x⁻¹*(b.val : G)*x
  have haB : a∈B := by
    simpa only [inv_inv] using (inferInstance : B.Normal).conj_mem _ b.property x⁻¹
  have haN : a∈N := hBN haB
  have haH : x*a*x⁻¹∈H := by
    have he : x*a*x⁻¹=(b.val : G) := by dsimp [a]; group
    rw [he]
    exact b.val.property
  let l0 : inducedOrbitStabilizer H N x := ⟨⟨a,haN⟩,haH⟩
  let l : inducedNormalCore H N B x := ⟨l0,haB⟩
  refine ⟨l,?_⟩
  apply Subtype.ext
  apply Subtype.ext
  change x*a*x⁻¹=(b.val : G)
  dsimp [a]
  group

include hBN in
theorem inducedNormalCore_dualOrbitCard [Finite G] [Finite k] [Finite V]
    [FiniteDimensional k V] (rho : Representation k H V) :
    Nat.card (Quotient (representationNonzeroOrbitRel
      (Representation.dual ((inducedOrbitFibre H N rho x).comp
        (inducedNormalCore H N B x).subtype))))=
      Nat.card (Quotient (representationNonzeroOrbitRel
        (Representation.dual (rho.comp (B.subgroupOf H).subtype)))) := by
  rw [FiniteRepresentationOrbitDuality.nonzero_orbit_card_dual,
    FiniteRepresentationOrbitDuality.nonzero_orbit_card_dual]
  have he : (inducedOrbitFibre H N rho x).comp (inducedNormalCore H N B x).subtype=
      (rho.comp (B.subgroupOf H).subtype).comp (inducedNormalCoreTwist H N B x) := rfl
  rw [he]
  exact nonzeroOrbitCard_comp_surjective _ _
    (inducedNormalCoreTwist_surjective H N B hBN x)

end SymmetricSubgroupAsymptotics
