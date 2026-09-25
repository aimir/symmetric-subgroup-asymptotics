import SymmetricSubgroupAsymptotics.CriticalProducts
import Mathlib.GroupTheory.SpecificGroups.Alternating

/-!
# The actual natural S3 marker and its binary contraction

The forced alternating kernel is proved by fourth powers in the actual
product group. Contraction preserves the complete exterior subgroup image,
so no original fullness condition is discarded. The marker contributes one
binary quotient coordinate in addition to all exterior coordinates.
-/

set_option autoImplicit false
noncomputable section

namespace SymmetricSubgroupAsymptotics

abbrev OddMarkerGroup := Equiv.Perm (Fin 3)

/-- The marker is the entire original symmetric group on its three points. -/
def oddMarkerActionSubgroup : Subgroup (Equiv.Perm (Fin 3)) := ⊤

theorem oddMarker_group_card : Nat.card OddMarkerGroup = 6 := by
  norm_num [Nat.card_eq_fintype_card, Fintype.card_perm]

theorem oddMarker_normalizer_card :
    Nat.card (Subgroup.normalizer (oddMarkerActionSubgroup : Set (Equiv.Perm (Fin 3)))) = 6 := by
  have ht : Subgroup.normalizer (oddMarkerActionSubgroup : Set (Equiv.Perm (Fin 3))) = ⊤ := by
    ext g
    change (∀ h : Equiv.Perm (Fin 3), h ∈ Set.univ ↔ g * h * g⁻¹ ∈ Set.univ) ↔ True
    simp
  rw [ht]
  norm_num [Nat.card_eq_fintype_card, Fintype.card_perm]

theorem oddMarker_transitive (x y : Fin 3) :
    ∃ g : oddMarkerActionSubgroup, (g : Equiv.Perm (Fin 3)) x = y := by
  exact ⟨⟨Equiv.swap x y, Subgroup.mem_top _⟩, Equiv.swap_apply_left x y⟩

private def oddSignUnitHom : ℤˣ →* Multiplicative (ZMod 2) where
  toFun z := Multiplicative.ofAdd (if z = 1 then 0 else 1)
  map_one' := by decide
  map_mul' z w := by
    rcases Int.units_eq_one_or z with rfl | rfl <;>
      rcases Int.units_eq_one_or w with rfl | rfl <;> decide

/-- The literal sign quotient, expressed as one binary coordinate. -/
def oddMarkerSign : OddMarkerGroup →* Multiplicative (ZMod 2) :=
  oddSignUnitHom.comp Equiv.Perm.sign

@[simp] theorem oddMarkerSign_eq_one (g : OddMarkerGroup) :
    oddMarkerSign g = 1 ↔ Equiv.Perm.sign g = 1 := by
  change Multiplicative.ofAdd (if Equiv.Perm.sign g = 1 then 0 else 1) = 1 ↔ _
  by_cases h : Equiv.Perm.sign g = 1 <;> simp [h]

theorem oddMarkerSign_surjective : Function.Surjective oddMarkerSign := by
  intro z
  have hz : z.toAdd = 0 ∨ z.toAdd = 1 := by
    have h : ∀ x : ZMod 2, x = 0 ∨ x = 1 := by decide
    exact h _
  rcases hz with hz | hz
  · refine ⟨1, ?_⟩
    apply Multiplicative.toAdd.injective
    simpa using hz.symm
  · refine ⟨Equiv.swap (0 : Fin 3) 1, ?_⟩
    apply Multiplicative.toAdd.injective
    change (if Equiv.Perm.sign (Equiv.swap (0 : Fin 3) 1) = 1 then (0 : ZMod 2) else 1) = z.toAdd
    rw [Equiv.Perm.sign_swap (by decide)]
    simpa using hz.symm

/-- Its kernel is exactly the actual natural alternating group. -/
theorem oddMarkerSign_ker : oddMarkerSign.ker = alternatingGroup (Fin 3) := by
  ext g
  exact oddMarkerSign_eq_one g

theorem oddMarker_kernel_card : Nat.card oddMarkerSign.ker = 3 := by
  rw [oddMarkerSign_ker, nat_card_alternatingGroup]
  norm_num

/-- The cube identity holds for every actual kernel permutation. -/
theorem oddMarker_kernel_cube (g : OddMarkerGroup) (hg : g ∈ oddMarkerSign.ker) :
    g ^ 3 = 1 := by
  have h := pow_card_eq_one' (x := (⟨g,hg⟩ : oddMarkerSign.ker))
  rw [oddMarker_kernel_card] at h
  exact congrArg Subtype.val h

/-- Every concrete binary Heisenberg group has exponent dividing four. -/
theorem binaryHeisenberg_pow_four {m : ℕ} (g : BinaryHeisenberg m) : g ^ 4 = 1 := by
  rw [show (4 : ℕ) = 2 * 2 from rfl, pow_mul, BinaryHeisenberg.square g,
    ← map_pow]
  have h : (Multiplicative.ofAdd (binaryDot g.b g.a) : Multiplicative (ZMod 2)) ^ 2 = 1 :=
    binary_mul_pow_two _
  rw [h, map_one]

/-- Thus the forced-kernel theorem applies to every concrete critical word. -/
theorem criticalProduct_pow_four {ι : Type*} [Fintype ι]
    (a : ℕ) (d : ι → Bool) (g : CriticalProductGroup a d) : g ^ 4 = 1 := by
  apply Prod.ext
  · change g.1 ^ 4 = 1
    rw [show (4 : ℕ) = 2 * 2 from rfl, pow_mul, binary_mul_pow_two]
  · funext i
    exact binaryHeisenberg_pow_four (g.2 i)

section Contraction

variable {D : Type*} [Group D]

/-- Quotient only the original marker coordinate. -/
def oddMarkerContraction : OddMarkerGroup × D →* Multiplicative (ZMod 2) × D :=
  oddMarkerSign.prodMap (MonoidHom.id D)

theorem oddMarkerContraction_surjective :
    Function.Surjective (oddMarkerContraction (D := D)) := by
  rintro ⟨z,d⟩
  obtain ⟨g,hg⟩ := oddMarkerSign_surjective z
  exact ⟨(g,d),Prod.ext hg rfl⟩

/-- The contraction kernel consists of A3 on the marker alone. -/
theorem mem_oddMarkerContraction_ker (g : OddMarkerGroup × D) :
    g ∈ (oddMarkerContraction (D := D)).ker ↔
      g.1 ∈ alternatingGroup (Fin 3) ∧ g.2 = 1 := by
  change (oddMarkerSign g.1, g.2) = (1,1) ↔ _
  rw [Prod.mk.injEq, ← oddMarkerSign_ker]
  rfl

/-- Fullness of the S3 projection forces the actual A3×1 kernel by taking
fourth powers. No coprime quotient or desired lift count is assumed. -/
theorem oddMarker_forced_kernel (hfour : ∀ d : D, d ^ 4 = 1)
    (H : Subgroup (OddMarkerGroup × D))
    (hfull : H.map (MonoidHom.fst OddMarkerGroup D) = ⊤) :
    (oddMarkerContraction (D := D)).ker ≤ H := by
  rintro ⟨g,d⟩ hg
  rcases (mem_oddMarkerContraction_ker _).mp hg with ⟨hg, rfl⟩
  have hm : g ∈ H.map (MonoidHom.fst OddMarkerGroup D) := by rw [hfull]; trivial
  obtain ⟨x,hx,hgx⟩ := Subgroup.mem_map.mp hm
  have hpow := H.pow_mem hx 4
  have hg3 : g ^ 3 = 1 := oddMarker_kernel_cube g (by simpa [oddMarkerSign_ker] using hg)
  have hg4 : g ^ 4 = g := by rw [show (4 : ℕ) = 3 + 1 from rfl, pow_succ, hg3, one_mul]
  have he : x ^ 4 = (g,1) := by
    apply Prod.ext
    · change x.1 ^ 4 = g
      change x.1 = g at hgx
      rw [hgx, hg4]
    · exact hfour x.2
  simpa only [he] using hpow

/-- Contraction preserves the entire exterior subgroup image, not merely
its order or a list of projected dimensions. -/
theorem oddMarkerContraction_exterior_image (H : Subgroup (OddMarkerGroup × D)) :
    (H.map oddMarkerContraction).map (MonoidHom.snd (Multiplicative (ZMod 2)) D) =
      H.map (MonoidHom.snd OddMarkerGroup D) := by
  rw [Subgroup.map_map]
  rfl

/-- A full S3 projection becomes a full binary marker projection. -/
theorem oddMarkerContraction_full (H : Subgroup (OddMarkerGroup × D))
    (hfull : H.map (MonoidHom.fst OddMarkerGroup D) = ⊤) :
    (H.map oddMarkerContraction).map (MonoidHom.fst (Multiplicative (ZMod 2)) D) = ⊤ := by
  apply top_unique
  intro z _
  obtain ⟨g,hg⟩ := oddMarkerSign_surjective z
  have hm : g ∈ H.map (MonoidHom.fst OddMarkerGroup D) := by rw [hfull]; trivial
  obtain ⟨x,hx,hgx⟩ := Subgroup.mem_map.mp hm
  refine Subgroup.mem_map.mpr ⟨oddMarkerContraction x,Subgroup.mem_map.mpr ⟨x,hx,rfl⟩,?_⟩
  change oddMarkerSign x.1 = z
  change x.1 = g at hgx
  rw [hgx,hg]

/-- Lifting a full binary marker subgroup restores the full original S3. -/
theorem oddMarkerContraction_comap_full
    (J : Subgroup (Multiplicative (ZMod 2) × D))
    (hfull : J.map (MonoidHom.fst (Multiplicative (ZMod 2)) D) = ⊤) :
    (J.comap oddMarkerContraction).map (MonoidHom.fst OddMarkerGroup D) = ⊤ := by
  apply top_unique
  intro g _
  have hm : oddMarkerSign g ∈ J.map (MonoidHom.fst (Multiplicative (ZMod 2)) D) := by
    rw [hfull]; trivial
  obtain ⟨x,hx,hxg⟩ := Subgroup.mem_map.mp hm
  refine Subgroup.mem_map.mpr ⟨(g,x.2),?_,rfl⟩
  change (oddMarkerSign g,x.2) ∈ J
  change x.1 = oddMarkerSign g at hxg
  simpa only [← hxg] using hx

/-- The inverse contraction also preserves the entire exterior image. -/
theorem oddMarkerContraction_comap_exterior_image
    (J : Subgroup (Multiplicative (ZMod 2) × D)) :
    (J.comap oddMarkerContraction).map (MonoidHom.snd OddMarkerGroup D) =
      J.map (MonoidHom.snd (Multiplicative (ZMod 2)) D) := by
  have h := oddMarkerContraction_exterior_image (J.comap oddMarkerContraction)
  rw [Subgroup.map_comap_eq_self (show J ≤ (oddMarkerContraction (D := D)).range by
    rw [MonoidHom.range_eq_top.mpr oddMarkerContraction_surjective]; exact le_top)] at h
  exact h.symm

/-- Actual marker-full subgroup contraction, with every exterior condition
retained as an arbitrary predicate on its literal subgroup image. -/
def oddMarkerContractionEquiv (hfour : ∀ d : D, d ^ 4 = 1) (P : Subgroup D → Prop) :
    {H : Subgroup (OddMarkerGroup × D) //
      H.map (MonoidHom.fst OddMarkerGroup D) = ⊤ ∧
        P (H.map (MonoidHom.snd OddMarkerGroup D))} ≃
    {J : Subgroup (Multiplicative (ZMod 2) × D) //
      J.map (MonoidHom.fst (Multiplicative (ZMod 2)) D) = ⊤ ∧
        P (J.map (MonoidHom.snd (Multiplicative (ZMod 2)) D))} where
  toFun H := ⟨H.1.map oddMarkerContraction, oddMarkerContraction_full H.1 H.2.1,
    by simpa only [oddMarkerContraction_exterior_image] using H.2.2⟩
  invFun J := ⟨J.1.comap oddMarkerContraction, oddMarkerContraction_comap_full J.1 J.2.1,
    by simpa only [oddMarkerContraction_comap_exterior_image] using J.2.2⟩
  left_inv H := Subtype.ext (Subgroup.comap_map_eq_self (oddMarker_forced_kernel hfour H.1 H.2.1))
  right_inv J := Subtype.ext (Subgroup.map_comap_eq_self (by
    rw [MonoidHom.range_eq_top.mpr oddMarkerContraction_surjective]; exact le_top))

/-- The contraction is a genuine cardinal identity on actual subgroups. -/
theorem oddMarkerContraction_card (hfour : ∀ d : D, d ^ 4 = 1) (P : Subgroup D → Prop) :
    Nat.card {H : Subgroup (OddMarkerGroup × D) //
      H.map (MonoidHom.fst OddMarkerGroup D) = ⊤ ∧ P (H.map (MonoidHom.snd OddMarkerGroup D))} =
    Nat.card {J : Subgroup (Multiplicative (ZMod 2) × D) //
      J.map (MonoidHom.fst (Multiplicative (ZMod 2)) D) = ⊤ ∧
        P (J.map (MonoidHom.snd (Multiplicative (ZMod 2)) D))} :=
  Nat.card_congr (oddMarkerContractionEquiv hfour P)

end Contraction

/-- Concrete critical products supply the exponent hypothesis; the exterior
predicate may retain all original C2/V4/D8/E8 projection conditions. -/
def oddCriticalProductContractionEquiv {ι : Type*} [Fintype ι]
    (a : ℕ) (d : ι → Bool) (P : Subgroup (CriticalProductGroup a d) → Prop) :=
  oddMarkerContractionEquiv (criticalProduct_pow_four a d) P

/-- The contracted marker adds one coordinate to the entire exterior
binary quotient. Thus exterior rank R−1 gives total rank R. -/
theorem oddCriticalProduct_total_quotient_rank {ι : Type*} [Fintype ι]
    (a : ℕ) (d : ι → Bool) :
    Module.finrank (ZMod 2) ((ZMod 2) × (Fin (criticalProductRank a d) → ZMod 2)) =
      criticalProductRank a d + 1 := by
  simp [Module.finrank_prod, Nat.add_comm]

/-- The contracted marker is installed as the first actual free binary
coordinate of the concrete critical product, without changing any D8/E8
factor or splitting an original V4 fullness condition. -/
def oddContractedCriticalEquiv {ι : Type*} [Fintype ι]
    (a : ℕ) (d : ι → Bool) :
    Multiplicative (ZMod 2) × CriticalProductGroup a d ≃* CriticalProductGroup (a + 1) d where
  toFun g := (Multiplicative.ofAdd (Fin.cons g.1.toAdd g.2.1.toAdd), g.2.2)
  invFun h := (Multiplicative.ofAdd (h.1.toAdd 0),
    (Multiplicative.ofAdd (fun i => h.1.toAdd i.succ), h.2))
  left_inv g := by
    apply Prod.ext
    · rfl
    · apply Prod.ext
      · rfl
      · rfl
  right_inv h := by
    apply Prod.ext
    · apply Multiplicative.toAdd.injective
      funext i
      refine Fin.cases ?_ (fun j => ?_) i <;> rfl
    · rfl
  map_mul' g h := by
    apply Prod.ext
    · apply Multiplicative.toAdd.injective
      funext i
      refine Fin.cases ?_ (fun j => ?_) i <;> rfl
    · rfl

/-- The actual full odd product has its binary quotient of total rank
one greater than the exterior rank. -/
def oddCriticalProductQuotient {ι : Type*} [Fintype ι]
    (a : ℕ) (d : ι → Bool) :
    OddMarkerGroup × CriticalProductGroup a d →*
      Multiplicative (Fin (criticalProductRank (a + 1) d) → ZMod 2) :=
  (criticalProductQuotient (a + 1) d).comp
    ((oddContractedCriticalEquiv a d).toMonoidHom.comp oddMarkerContraction)

theorem oddCriticalProductQuotient_surjective {ι : Type*} [Fintype ι]
    (a : ℕ) (d : ι → Bool) : Function.Surjective (oddCriticalProductQuotient a d) :=
  (criticalProductQuotient_surjective (a + 1) d).comp
    ((oddContractedCriticalEquiv a d).surjective.comp oddMarkerContraction_surjective)

theorem oddCriticalProduct_rank {ι : Type*} [Fintype ι]
    (a : ℕ) (d : ι → Bool) : criticalProductRank (a + 1) d = criticalProductRank a d + 1 := by
  unfold criticalProductRank
  omega

/-- In the S3 branch the exterior rank is R−1 but the Gaussian rank is R. -/
theorem oddCriticalProduct_rank_of_exterior {ι : Type*} [Fintype ι]
    (a : ℕ) (d : ι → Bool) (R : ℕ) (hR : 0 < R)
    (hexterior : criticalProductRank a d = R - 1) : criticalProductRank (a + 1) d = R := by
  rw [oddCriticalProduct_rank, hexterior]
  omega

end SymmetricSubgroupAsymptotics
