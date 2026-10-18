import SymmetricSubgroupAsymptotics.PrimeRelativeRadicalImage

/-! A full original top image makes the retained relative-radical quotient
abelian. The supplement remains the actual abelian flip kernel; no splitting
or extension of characters from a subgroup is assumed. -/

set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.TwelvePointRemainingStructural

variable {G H : Type} [Group G] [Group H]

/-- An abelian supplement and a central image of the normal subgroup
make the entire actual surjective image commutative. -/
theorem image_commutative_of_abelian_supplement
    (K M : Subgroup G) [M.Normal] (hKM : K ⊔ M = ⊤)
    (hK : IsMulCommutative K) (f : G →* H) (hf : Function.Surjective f)
    (hM : M.map f ≤ Subgroup.center H) : IsMulCommutative H := by
  letI := hK
  refine ⟨⟨?_⟩⟩
  intro x y
  obtain ⟨g, rfl⟩ := hf x
  obtain ⟨h, rfl⟩ := hf y
  obtain ⟨k, hk, m, hm, rfl⟩ := Subgroup.mem_sup_of_normal_right.mp
    (show g ∈ K ⊔ M by rw [hKM]; trivial)
  obtain ⟨l, hl, n, hn, rfl⟩ := Subgroup.mem_sup_of_normal_right.mp
    (show h ∈ K ⊔ M by rw [hKM]; trivial)
  have hmZ : f m ∈ Subgroup.center H := hM ⟨m, hm, rfl⟩
  have hnZ : f n ∈ Subgroup.center H := hM ⟨n, hn, rfl⟩
  have hml : f m * f l = f l * f m :=
    (Subgroup.mem_center_iff.mp hmZ (f l)).symm
  have hmn : f m * f n = f n * f m :=
    (Subgroup.mem_center_iff.mp hmZ (f n)).symm
  have hkn : f k * f n = f n * f k :=
    Subgroup.mem_center_iff.mp hnZ (f k)
  have hkl : f k * f l = f l * f k := by
    rw [← map_mul, ← map_mul]
    exact congrArg f (congrArg (fun z : K => (z : G))
      (hK.is_comm.comm (⟨k,hk⟩ : K) (⟨l,hl⟩ : K)))
  rw [map_mul, map_mul]
  calc
    (f k * f m) * (f l * f n) = f k * (f m * f l) * f n := by group
    _ = f k * (f l * f m) * f n := by rw [hml]
    _ = (f k * f l) * (f m * f n) := by group
    _ = (f l * f k) * (f n * f m) := by rw [hkl, hmn]
    _ = f l * (f k * f n) * f m := by group
    _ = f l * (f n * f k) * f m := by rw [hkn]
    _ = (f l * f n) * (f k * f m) := by group

/-- This applies to the literal relative radical of the actual M. Its
quotient may have higher exponent; it is not replaced by an elementary
abelian quotient before the subgroup-rank step. -/
theorem relativeRadicalQuotient_commutative
    (p : ℕ) [Fact p.Prime] (K M : Subgroup G) [M.Normal]
    (hKM : K ⊔ M = ⊤) (hK : IsMulCommutative K) :
    IsMulCommutative (G ⧸ primeRelativeRadical p M) := by
  apply image_commutative_of_abelian_supplement K M hKM hK
    (QuotientGroup.mk' (primeRelativeRadical p M))
    (QuotientGroup.mk'_surjective _)
  exact primeRelativeRadical_image_le_center p M

end SymmetricSubgroupAsymptotics.TwelvePointRemainingStructural
