import SymmetricSubgroupAsymptotics.SignedMonomialSupportOrbitIndex

/-! A fixed monomial vector is determined by its scalars on zero
coordinates and its ACTUAL projected permutation. Retaining the latter
inside the same top's support-set stabilizer gives a cardinal bound
without replacing that top by a full symmetric group. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Classical Pointwise
namespace SymmetricSubgroupAsymptotics.SignedMonomialFixedTopCode
open SignedMonomialFixedCoordinateCode SignedMonomialStabilizerClassBound

def supportTopStabilizer {G I K : Type*} [Group G] [Field K]
    (t : G →* Equiv.Perm I) (v : I → K) : Subgroup t.range :=
  (MulAction.stabilizer (Equiv.Perm I) {i : I | v i≠0}).comap t.range.subtype

theorem fixed_card_le_zero_units_mul_top_stabilizer
    {G I K : Type*} [Group G] [Field K] [Finite G] [Finite I] [Finite K]
    (ρ : G →* ((I → K) ≃ₗ[K] (I → K)))
    (t : G →* Equiv.Perm I) (a : G → I → Kˣ)
    (hformula : ∀ (g : G) (w : I → K) (i : I),
      ρ g w i=(a g i : K)*w ((t g).symm i))
    (hρ : Function.Injective ρ) (v : I → K) :
    Nat.card (fixedSubgroup ρ v)≤
      Nat.card Kˣ ^ Nat.card {i : I // v i=0} * Nat.card (supportTopStabilizer t v) := by
  letI : Finite t.range := Finite.of_surjective t.rangeRestrict t.rangeRestrict_surjective
  letI : Finite Kˣ := Finite.of_injective (fun u : Kˣ => (u : K)) Units.val_injective
  let b : fixedSubgroup ρ v → supportTopStabilizer t v := fun g =>
    ⟨⟨t g.val,⟨g.val,rfl⟩⟩,by
      change t g.val • {i : I | v i≠0}={i : I | v i≠0}
      apply Set.ext
      intro i
      simp only [Set.mem_smul_set_iff_inv_smul_mem,Set.mem_setOf_eq]
      change v ((t g.val).symm i)≠0 ↔ v i≠0
      have h := fixed_support_iff ρ t a hformula g.val v g.property ((t g.val).symm i)
      simpa only [Equiv.apply_symm_apply] using h.symm⟩
  let code : fixedSubgroup ρ v →
      ({i : I // v i=0} → Kˣ) × supportTopStabilizer t v :=
    fun g => (fun i => a g.val i.val,b g)
  have hinj : Function.Injective code := by
    intro g h he
    apply Subtype.ext
    apply fixed_element_eq_of_zero_coefficients ρ t a hformula hρ v
      g.val h.val g.property h.property
    · exact congrArg (fun z : supportTopStabilizer t v => z.val.val) (congrArg Prod.snd he)
    · intro i hi
      exact congrFun (congrArg Prod.fst he) ⟨i,hi⟩
  calc
    _≤Nat.card (({i : I // v i=0} → Kˣ) × supportTopStabilizer t v) :=
      Nat.card_le_card_of_injective code hinj
    _=_ := by rw [Nat.card_prod,Nat.card_fun]

end SymmetricSubgroupAsymptotics.SignedMonomialFixedTopCode
