import SymmetricSubgroupAsymptotics.EquivariantOrbitFibreCard

/-! Exact orbit scaling when an actual subgroup fills the original fibre.
No split extension, independent coordinate action, or orbit-size premise. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.EquivariantOrbitFibreExact

variable {G X I : Type} [Group G] [MulAction G X] [MulAction G I]

/-- Transport a literal fibre orbit over every point of the block orbit. -/
def orbitProductEquiv (b : X → I)
    (hb : ∀ (g : G) (y : X), b (g • y) = g • b y)
    (K : Subgroup G) (x : X)
    (hK : ∀ k : K, (k : G) • b x = b x)
    (hfill : ∀ y : X, b y = b x → y ∈ MulAction.orbit K x) :
    MulAction.orbit G (b x) × MulAction.orbit K x ≃ MulAction.orbit G x := by
  classical
  let t : MulAction.orbit G (b x) → G := fun i =>
    Classical.choose (MulAction.mem_orbit_iff.mp i.property)
  have ht (i : MulAction.orbit G (b x)) : t i • b x = (i : I) :=
    Classical.choose_spec (MulAction.mem_orbit_iff.mp i.property)
  have hz (z : MulAction.orbit K x) : b (z : X) = b x := by
    obtain ⟨k, hk⟩ := MulAction.mem_orbit_iff.mp z.property
    rw [← hk]
    exact (hb k x).trans (hK k)
  let f : MulAction.orbit G (b x) × MulAction.orbit K x → MulAction.orbit G x :=
    fun iz => ⟨t iz.1 • (iz.2 : X), MulAction.mem_orbit_of_mem_orbit _
      (MulAction.mem_orbit_of_mem_orbit_subgroup iz.2.property)⟩
  apply Equiv.ofBijective f
  constructor
  · rintro ⟨i,z⟩ ⟨j,w⟩ he
    have he' : t i • (z : X) = t j • (w : X) := congrArg Subtype.val he
    have hi : i = j := by
      apply Subtype.ext
      have hh := congrArg b he'
      rw [hb, hb, hz, hz, ht, ht] at hh
      exact hh
    subst j
    have hw : z = w := Subtype.ext ((MulAction.injective (t i)) he')
    subst w
    rfl
  · intro y
    have hby : b (y : X) ∈ MulAction.orbit G (b x) := by
      obtain ⟨g,hg⟩ := MulAction.mem_orbit_iff.mp y.property
      apply MulAction.mem_orbit_iff.mpr
      exact ⟨g, (hb g x).symm.trans (congrArg b hg)⟩
    let i : MulAction.orbit G (b x) := ⟨b (y : X), hby⟩
    have hti : t i • b x = b (y : X) := ht i
    have hbase : b ((t i)⁻¹ • (y : X)) = b x := by
      rw [hb, ← hti]
      exact inv_smul_smul (t i) (b x)
    let z : MulAction.orbit K x := ⟨(t i)⁻¹ • (y : X), hfill _ hbase⟩
    refine ⟨(i,z), ?_⟩
    apply Subtype.ext
    exact smul_inv_smul (t i) (y : X)

/-- Every point of the block orbit has the complete original fibre. -/
theorem orbit_card_eq_block_mul_fibre [Finite X] [Finite I]
    (b : X → I) (hb : ∀ (g : G) (y : X), b (g • y) = g • b y)
    (K : Subgroup G) (x : X)
    (hK : ∀ k : K, (k : G) • b x = b x)
    (hfill : ∀ y : X, b y = b x → y ∈ MulAction.orbit K x) :
    Nat.card (MulAction.orbit G x) =
      Nat.card (MulAction.orbit G (b x)) * Nat.card (MulAction.orbit K x) := by
  simpa only [Nat.card_prod] using
    (Nat.card_congr (orbitProductEquiv b hb K x hK hfill)).symm

end SymmetricSubgroupAsymptotics.EquivariantOrbitFibreExact
