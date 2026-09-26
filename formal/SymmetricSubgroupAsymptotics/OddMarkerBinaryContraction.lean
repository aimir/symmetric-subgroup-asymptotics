import SymmetricSubgroupAsymptotics.OddMarker
import Mathlib.GroupTheory.PGroup

/-! The original natural S3 marker over an arbitrary binary exterior.
The forced A3 kernel uses an elementwise power `4^k`, so no exponent-four
assumption on the exterior is needed. The literal sign contraction fixes
the entire exterior image. Arbitrary original predicates and weights are
evaluated after exact inverse reconstruction; no physical C2 normalizer
is substituted for the original S3 normalizer. -/
set_option autoImplicit false
noncomputable section
open scoped BigOperators Classical

namespace SymmetricSubgroupAsymptotics

private theorem oddMarker_kernel_pow_four_pow (g : OddMarkerGroup)
    (hg : g ∈ oddMarkerSign.ker) (k : ℕ) : g^(4^k)=g := by
  have hg4 : g^4=g := by
    rw [show (4 : ℕ)=3+1 by rfl, pow_succ, oddMarker_kernel_cube g hg, one_mul]
  induction k with
  | zero => simp
  | succ k ih => rw [pow_succ, pow_mul, ih, hg4]

section Binary

variable {D : Type*} [Group D]

/-- A marker-full subgroup contains A3 on the original marker alone.
The exterior may be any 2-group: an elementwise power suffices. -/
theorem oddMarker_forced_kernel_of_isPGroup (hD : IsPGroup 2 D)
    (H : Subgroup (OddMarkerGroup × D))
    (hfull : H.map (MonoidHom.fst OddMarkerGroup D)=⊤) :
    (oddMarkerContraction (D := D)).ker ≤ H := by
  rintro ⟨g,d⟩ hg
  rcases (mem_oddMarkerContraction_ker _).mp hg with ⟨hg,rfl⟩
  have hm : g ∈ H.map (MonoidHom.fst OddMarkerGroup D) := by rw [hfull]; trivial
  obtain ⟨x,hx,hgx⟩ := Subgroup.mem_map.mp hm
  obtain ⟨k,hk⟩ := hD x.2
  have hd : x.2^(4^k)=1 := by
    rw [show (4 : ℕ)^k=2^k*2^k by simpa using (mul_pow (2 : ℕ) 2 k),
      pow_mul, hk, one_pow]
  have he : x^(4^k)=(g,1) := by
    apply Prod.ext
    · change x.1^(4^k)=g
      change x.1=g at hgx
      rw [hgx]
      exact oddMarker_kernel_pow_four_pow g (by simpa only [oddMarkerSign_ker] using hg) k
    · exact hd
  simpa only [he] using H.pow_mem hx (4^k)

/-- A certified actual order `2^u` supplies the binary-exterior hypothesis. -/
theorem oddMarker_forced_kernel_of_card (u : ℕ) (hD : Nat.card D=2^u)
    (H : Subgroup (OddMarkerGroup × D))
    (hfull : H.map (MonoidHom.fst OddMarkerGroup D)=⊤) :
    (oddMarkerContraction (D := D)).ker ≤ H :=
  oddMarker_forced_kernel_of_isPGroup (IsPGroup.of_card hD) H hfull

/-- Exact contraction with the complete exterior condition retained.
Projection to the entire exterior need not be surjective. -/
def oddMarkerBinaryContractionEquiv (hD : IsPGroup 2 D) (P : Subgroup D → Prop) :
    {H : Subgroup (OddMarkerGroup × D) //
      H.map (MonoidHom.fst OddMarkerGroup D)=⊤ ∧
        P (H.map (MonoidHom.snd OddMarkerGroup D))} ≃
    {J : Subgroup (Multiplicative (ZMod 2) × D) //
      J.map (MonoidHom.fst (Multiplicative (ZMod 2)) D)=⊤ ∧
        P (J.map (MonoidHom.snd (Multiplicative (ZMod 2)) D))} where
  toFun H := ⟨H.1.map oddMarkerContraction, oddMarkerContraction_full H.1 H.2.1,
    by simpa only [oddMarkerContraction_exterior_image] using H.2.2⟩
  invFun J := ⟨J.1.comap oddMarkerContraction, oddMarkerContraction_comap_full J.1 J.2.1,
    by simpa only [oddMarkerContraction_comap_exterior_image] using J.2.2⟩
  left_inv H := Subtype.ext (Subgroup.comap_map_eq_self
    (oddMarker_forced_kernel_of_isPGroup hD H.1 H.2.1))
  right_inv J := Subtype.ext (Subgroup.map_comap_eq_self (by
    rw [MonoidHom.range_eq_top.mpr oddMarkerContraction_surjective]; exact le_top))

theorem oddMarkerBinaryContraction_reconstruct (hD : IsPGroup 2 D)
    (H : Subgroup (OddMarkerGroup × D))
    (hfull : H.map (MonoidHom.fst OddMarkerGroup D)=⊤) :
    (H.map oddMarkerContraction).comap oddMarkerContraction=H :=
  Subgroup.comap_map_eq_self (oddMarker_forced_kernel_of_isPGroup hD H hfull)

/-- A condition on the full original subgroup is tested on its exact
inverse comap. No invariance or factorization of that condition is assumed. -/
def oddMarkerBinaryContractionFilteredEquiv (hD : IsPGroup 2 D)
    (P : Subgroup D → Prop) (Q : Subgroup (OddMarkerGroup × D) → Prop) :
    {H : Subgroup (OddMarkerGroup × D) //
      H.map (MonoidHom.fst OddMarkerGroup D)=⊤ ∧
        P (H.map (MonoidHom.snd OddMarkerGroup D)) ∧ Q H} ≃
    {J : Subgroup (Multiplicative (ZMod 2) × D) //
      J.map (MonoidHom.fst (Multiplicative (ZMod 2)) D)=⊤ ∧
        P (J.map (MonoidHom.snd (Multiplicative (ZMod 2)) D)) ∧
          Q (J.comap oddMarkerContraction)} where
  toFun H := ⟨H.1.map oddMarkerContraction, oddMarkerContraction_full H.1 H.2.1,
    by simpa only [oddMarkerContraction_exterior_image] using H.2.2.1,
    by rw [oddMarkerBinaryContraction_reconstruct hD H.1 H.2.1]; exact H.2.2.2⟩
  invFun J := ⟨J.1.comap oddMarkerContraction, oddMarkerContraction_comap_full J.1 J.2.1,
    by simpa only [oddMarkerContraction_comap_exterior_image] using J.2.2.1, J.2.2.2⟩
  left_inv H := Subtype.ext (oddMarkerBinaryContraction_reconstruct hD H.1 H.2.1)
  right_inv J := Subtype.ext (Subgroup.map_comap_eq_self (by
    rw [MonoidHom.range_eq_top.mpr oddMarkerContraction_surjective]; exact le_top))

theorem oddMarkerBinaryContraction_card (hD : IsPGroup 2 D) (P : Subgroup D → Prop) :
    Nat.card {H : Subgroup (OddMarkerGroup × D) //
      H.map (MonoidHom.fst OddMarkerGroup D)=⊤ ∧ P (H.map (MonoidHom.snd OddMarkerGroup D))} =
    Nat.card {J : Subgroup (Multiplicative (ZMod 2) × D) //
      J.map (MonoidHom.fst (Multiplicative (ZMod 2)) D)=⊤ ∧
        P (J.map (MonoidHom.snd (Multiplicative (ZMod 2)) D))} :=
  Nat.card_congr (oddMarkerBinaryContractionEquiv hD P)

section Finite
variable [Finite D]

local instance subgroupFinite {G : Type*} [Group G] [Finite G] :
    Finite (Subgroup G) :=
  Finite.of_injective (fun H : Subgroup G => (H : Set G)) SetLike.coe_injective

attribute [local instance] Fintype.ofFinite

/-- Every original physical weight is retained on the original subgroup.
In particular the original marker normalizer factor remains `1/6`. -/
theorem oddMarkerBinaryContraction_weight_sum (hD : IsPGroup 2 D)
    (P : Subgroup D → Prop) (Q : Subgroup (OddMarkerGroup × D) → Prop)
    (W : Subgroup (OddMarkerGroup × D) → ℝ) :
    (∑ H : {H : Subgroup (OddMarkerGroup × D) //
      H.map (MonoidHom.fst OddMarkerGroup D)=⊤ ∧
        P (H.map (MonoidHom.snd OddMarkerGroup D)) ∧ Q H}, W H.1) =
    ∑ J : {J : Subgroup (Multiplicative (ZMod 2) × D) //
      J.map (MonoidHom.fst (Multiplicative (ZMod 2)) D)=⊤ ∧
        P (J.map (MonoidHom.snd (Multiplicative (ZMod 2)) D)) ∧
          Q (J.comap oddMarkerContraction)}, W (J.1.comap oddMarkerContraction) := by
  exact ((oddMarkerBinaryContractionFilteredEquiv hD P Q).symm.sum_comp
    (fun H => W H.1)).symm

end Finite
end Binary
end SymmetricSubgroupAsymptotics
