import SymmetricSubgroupAsymptotics.C1ComplementChart

/-! # Literal oriented character reconstruction
An order-three witness and the actual kernel reconstruct the source and the
oriented character. No quotient by automorphisms or complements occurs.
-/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics
variable {G : Type*} [Group G]

theorem ternaryCharacter_kernel_sup (χ : PrimeCharacters 3 G) (x : G)
    (hx : χ (Additive.ofMul x) = 1) :
    (ternaryCharacterHom χ).ker ⊔ Subgroup.zpowers x = ⊤ := by
  have hx' : ternaryCharacterHom χ x = ternaryGenerator := congrArg Multiplicative.ofAdd hx
  apply top_unique
  intro g _
  obtain ⟨n,hn⟩ := ternaryGenerator_generates (ternaryCharacterHom χ g)
  have ha : g * x^(-n) ∈ (ternaryCharacterHom χ).ker := by
    change ternaryCharacterHom χ (g*x^(-n)) = 1
    rw [map_mul,map_zpow,hx',← hn,zpow_neg,mul_inv_cancel]
  have hb : x^n ∈ Subgroup.zpowers x := ⟨n,rfl⟩
  have hh := Subgroup.mul_mem ((ternaryCharacterHom χ).ker ⊔ Subgroup.zpowers x)
    ((show (ternaryCharacterHom χ).ker ≤ _ from le_sup_left) ha)
    ((show Subgroup.zpowers x ≤ _ from le_sup_right) hb)
  simpa only [zpow_neg,mul_assoc,inv_mul_cancel,mul_one] using hh

theorem ternaryCharacter_ext_kernel_witness (χ ψ : PrimeCharacters 3 G)
    (hk : (ternaryCharacterHom χ).ker = (ternaryCharacterHom ψ).ker)
    (x : G) (hx : χ (Additive.ofMul x) = 1) (hy : ψ (Additive.ofMul x) = 1) : χ = ψ := by
  have he : (⊤ : Subgroup G) ≤
      (ternaryCharacterHom χ).eqLocus (ternaryCharacterHom ψ) := by
    rw [← ternaryCharacter_kernel_sup χ x hx]
    apply sup_le
    · intro g hg
      change ternaryCharacterHom χ g = ternaryCharacterHom ψ g
      have hg' : g ∈ (ternaryCharacterHom ψ).ker := hk ▸ hg
      exact hg.trans hg'.symm
    · apply Subgroup.zpowers_le.mpr
      exact congrArg Multiplicative.ofAdd (hx.trans hy.symm)
  apply AddMonoidHom.toMultiplicativeRight.injective
  exact MonoidHom.ext (fun g => he (Subgroup.mem_top g))

theorem ternaryCharacter_kernel_disjoint (χ : PrimeCharacters 3 G)
    (x : G) (ho : orderOf x = 3) (hx : χ (Additive.ofMul x) = 1) :
    Disjoint (ternaryCharacterHom χ).ker (Subgroup.zpowers x) := by
  apply Subgroup.disjoint_def.mpr
  intro g hg hz
  obtain ⟨n,rfl⟩ := hz
  have hgen : ternaryGenerator ^ n = 1 := by
    have hx' : ternaryCharacterHom χ x = ternaryGenerator := congrArg Multiplicative.ofAdd hx
    change ternaryCharacterHom χ (x^n) = 1 at hg
    simpa only [map_zpow,hx'] using hg
  have hd := (orderOf_dvd_iff_zpow_eq_one).mpr hgen
  apply orderOf_dvd_iff_zpow_eq_one.mp
  simpa only [ho,ternaryGenerator_order] using hd

/-- The source of a split character reconstructed in its original ambient group. -/
theorem ternaryCharacter_ambient_source (K : Subgroup G) (χ : PrimeCharacters 3 K)
    (x : K) (hx : χ (Additive.ofMul x) = 1) :
    (ternaryCharacterHom χ).ker.map K.subtype ⊔ Subgroup.zpowers (x:G) = K := by
  have h := congrArg (fun L : Subgroup K => L.map K.subtype)
    (ternaryCharacter_kernel_sup χ x hx)
  simpa only [Subgroup.map_sup,MonoidHom.map_zpowers,← MonoidHom.range_eq_map,
    Subgroup.range_subtype] using h

/-- Every original witness produces a literal complement chart. -/
def ternaryWitnessChart (K : Subgroup G) (χ : PrimeCharacters 3 K)
    (x : K) (ho : orderOf x = 3) (hx : χ (Additive.ofMul x) = 1) :
    TernaryComplementChart G where
  kernel := (ternaryCharacterHom χ).ker.map K.subtype
  generator := x
  generator_order := (Subgroup.orderOf_mk x.1 x.2).symm.trans ho
  normalizes := (ternaryCharacterHom χ).ker.le_normalizer_map K.subtype
    ⟨x,by rw [Subgroup.normalizer_eq_top]; trivial,rfl⟩
  disjoint := by
    rw [show Subgroup.zpowers (x : G) = (Subgroup.zpowers x).map K.subtype from
      (MonoidHom.map_zpowers K.subtype x).symm]
    exact Subgroup.disjoint_map K.subtype_injective
      (ternaryCharacter_kernel_disjoint χ x ho hx)

theorem ternaryWitnessChart_source (K : Subgroup G) (χ : PrimeCharacters 3 K)
    (x : K) (ho : orderOf x = 3) (hx : χ (Additive.ofMul x) = 1) :
    (ternaryWitnessChart K χ x ho hx).source = K :=
  ternaryCharacter_ambient_source K χ x hx

end SymmetricSubgroupAsymptotics
