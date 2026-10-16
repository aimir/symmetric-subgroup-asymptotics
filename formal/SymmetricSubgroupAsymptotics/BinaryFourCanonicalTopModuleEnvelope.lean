import SymmetricSubgroupAsymptotics.BinaryFourCanonicalTopKleinEnvelope
import SymmetricSubgroupAsymptotics.RepresentationIntertwinerGenerators
import Mathlib.LinearAlgebra.Dimension.Free

/-! Linear top-slot endpoint from the actual elementary top image and its
original conjugation law. The actual normal denominator is split into
zero/nonzero cases; no source module or quotient group is replaced. -/
set_option autoImplicit false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics.BinaryFourCanonicalTopModuleEnvelope
open BinaryFourBlockAugmentation BinaryFourSymmetricBlockActions

def TopSupport (x : SymmetricEnvelope) : Prop :=
  x.1 0 = 0 ∧ x.1 1 = 0 ∧ x.2.1 = 0

variable {R V W : Type} [Group R] [AddCommGroup V] [Module Scalar V]
  [AddCommGroup W] [Module Scalar W]

def linearize (f : Multiplicative V →* Multiplicative W) : V →ₗ[Scalar] W :=
  (AddMonoidHom.toMultiplicative.symm f).toZModLinearMap 2

theorem linearize_injective (f : Multiplicative V →* Multiplicative W)
    (hf : Function.Injective f) : Function.Injective (linearize f) := by
  intro x y h
  exact Multiplicative.ofAdd.injective (hf (congrArg Multiplicative.ofAdd h))

def scalarSlot : Scalar →ₗ[Scalar] SymmetricEnvelope where
  toFun a := (fun j => if j = 2 then a else 0,0,0)
  map_add' a b := by
    apply Prod.ext
    · funext j
      change (if j=2 then a+b else 0) =
        (if j=2 then a else 0)+(if j=2 then b else 0)
      split_ifs <;> simp
    · simp
  map_smul' a b := by ext j <;> simp

theorem scalarSlot_injective : Function.Injective scalarSlot := by
  intro a b h
  exact congrArg (fun z : SymmetricEnvelope => z.1 2) h

theorem scalarSlot_fixed (g : SymmetricComplement) (a : Scalar) :
    symmetricEnvelopeRepresentation g (scalarSlot a) = scalarSlot a := by
  rcases g with ⟨⟨p,z⟩,b⟩
  revert p z b a
  decide +kernel

private theorem scalar_injection_of_card_le_two [FiniteDimensional Scalar V] [Finite V]
    (hc : Nat.card V ≤ 2) : ∃ j : V →ₗ[Scalar] Scalar, Function.Injective j := by
  have hpow : 2 ^ Module.finrank Scalar V ≤ 2 ^ 1 := by
    simpa only [Module.natCard_eq_pow_finrank (K := Scalar) (V := V),Nat.card_zmod,pow_one] using hc
  have hd : Module.finrank Scalar V ≤ 1 :=
    (Nat.pow_le_pow_iff_right (by decide : 1 < (2 : ℕ))).mp hpow
  by_cases hz : Module.finrank Scalar V = 0
  · letI : Subsingleton V := (Module.finrank_eq_zero_iff_of_free Scalar V).mp hz
    exact ⟨0,fun _ _ _ => Subsingleton.elim _ _⟩
  · have he : Module.finrank Scalar V = Module.finrank Scalar Scalar := by
      rw [Module.finrank_self]
      omega
    let e : V ≃ₗ[Scalar] Scalar := LinearEquiv.ofFinrankEq V Scalar he
    exact ⟨e.toLinearMap,e.injective⟩

/-- Nonzero actual S4 normal denominators leave at most one TRIVIAL top
slot. The supplied injection and conjugation identity are actual maps. -/
theorem nonzero_top_intertwiner [FiniteDimensional Scalar V]
    (N : Subgroup SymmetricComplement) [N.Normal] (hN : N ≠ ⊥)
    (beta : R →* SymmetricComplement) (rho : Representation Scalar R V)
    (f : Multiplicative V →* SymmetricComplement ⧸ N) (hf : Function.Injective f)
    (hH : f.range.Normal) (hbinary : IsPGroup 2 f.range)
    (hconj : ∀ r v, f (Multiplicative.ofAdd (rho r v)) =
      QuotientGroup.mk' N (beta r) * f (Multiplicative.ofAdd v) *
        (QuotientGroup.mk' N (beta r))⁻¹) :
    ∃ i : rho.IntertwiningMap (symmetricEnvelopeRepresentation.comp beta),
      Function.Injective i ∧ ∀ v, TopSupport (i v) := by
  letI : f.range.Normal := hH
  letI : Finite V := Finite.of_injective
    (fun v : V => f (Multiplicative.ofAdd v)) (hf.comp Multiplicative.ofAdd.injective)
  have hc : Nat.card V ≤ 2 := by
    have he : Nat.card V = Nat.card f.range :=
      Nat.card_congr (Multiplicative.ofAdd.trans
        (MulEquiv.ofBijective f.rangeRestrict ⟨(fun _ _ h => hf (congrArg Subtype.val h)),f.rangeRestrict_surjective⟩).toEquiv)
    rcases BinaryFourCanonicalTopBinaryQuotients.s4_nonzero_binary_card N hN f.range hbinary with h | h
    · omega
    · omega
  obtain ⟨j,hj⟩ := scalar_injection_of_card_le_two hc
  have hcentral := BinaryFourCanonicalTopBinaryQuotients.s4_nonzero_binary_normal_central
    N hN f.range hbinary
  have hfixed (r : R) (v : V) : rho r v = v := by
    apply Multiplicative.ofAdd.injective
    apply hf
    rw [hconj]
    have hcomm := Subgroup.mem_center_iff.mp
      (hcentral (show f (Multiplicative.ofAdd v) ∈ f.range from ⟨_,rfl⟩))
      (QuotientGroup.mk' N (beta r))
    rw [hcomm]
    simp only [mul_assoc,mul_inv_cancel,mul_one]
  let i : rho.IntertwiningMap (symmetricEnvelopeRepresentation.comp beta) := {
    toLinearMap := scalarSlot.comp j
    isIntertwining' r := by
      apply LinearMap.ext
      intro v
      change scalarSlot (j (rho r v)) =
        symmetricEnvelopeRepresentation (beta r) (scalarSlot (j v))
      rw [hfixed,scalarSlot_fixed] }
  exact ⟨i,scalarSlot_injective.comp hj,fun _ => ⟨rfl,rfl,rfl⟩⟩

/-- Zero actual normal denominator: the normal binary image lies in
literal Klein and occupies the second active plane with its odd action. -/
theorem unquotiented_top_intertwiner
    (beta : R →* SymmetricComplement) (rho : Representation Scalar R V)
    (f : Multiplicative V →* SymmetricComplement) (hf : Function.Injective f)
    (hH : f.range.Normal) (hbinary : IsPGroup 2 f.range)
    (hconj : ∀ r v, f (Multiplicative.ofAdd (rho r v)) =
      beta r * f (Multiplicative.ofAdd v) * (beta r)⁻¹) :
    ∃ i : rho.IntertwiningMap (symmetricEnvelopeRepresentation.comp beta),
      Function.Injective i ∧ ∀ v, TopSupport (i v) := by
  letI : f.range.Normal := hH
  have hK := BinaryFourCanonicalTopBinaryQuotients.s4_binary_normal_le_klein f.range hbinary
  let k : Multiplicative V →* BinaryFourSymmetricKleinNormalCover.klein :=
    (Subgroup.inclusion hK).comp f.rangeRestrict
  let a : Multiplicative V →* Multiplicative SymmetricEnvelope :=
    BinaryFourCanonicalTopKleinEnvelope.kleinEmbedding.comp k
  have hk (r : R) (v : V) :
      k (Multiplicative.ofAdd (rho r v)) = MulAut.conjNormal (beta r) (k (Multiplicative.ofAdd v)) :=
    Subtype.ext (hconj r v)
  let i : rho.IntertwiningMap (symmetricEnvelopeRepresentation.comp beta) := {
    toLinearMap := linearize a
    isIntertwining' r := by
      apply LinearMap.ext
      intro v
      change (BinaryFourCanonicalTopKleinEnvelope.kleinEmbedding
        (k (Multiplicative.ofAdd (rho r v)))).toAdd =
        symmetricEnvelopeRepresentation (beta r)
          (BinaryFourCanonicalTopKleinEnvelope.kleinEmbedding (k (Multiplicative.ofAdd v))).toAdd
      rw [hk]
      exact BinaryFourCanonicalTopKleinEnvelope.conjugate _ _ }
  have hkInj : Function.Injective k :=
    (Subgroup.inclusion_injective hK).comp (fun _ _ h => hf (congrArg Subtype.val h))
  exact ⟨i,linearize_injective a
    (BinaryFourCanonicalTopKleinEnvelope.kleinEmbedding_injective.comp hkInj),
      fun _ => ⟨rfl,rfl,rfl⟩⟩

/-- The A4 zero-denominator case uses its ACTUAL even action. No normal
bound is inherited from the S4 ambient group. -/
theorem a4_unquotiented_top_intertwiner
    (beta : R →* Complement) (rho : Representation Scalar R V)
    (f : Multiplicative V →* Complement) (hf : Function.Injective f)
    (hH : f.range.Normal) (hbinary : IsPGroup 2 f.range)
    (hconj : ∀ r v, f (Multiplicative.ofAdd (rho r v)) =
      beta r * f (Multiplicative.ofAdd v) * (beta r)⁻¹) :
    ∃ i : rho.IntertwiningMap
        (symmetricEnvelopeRepresentation.comp (SemidirectProduct.inl.comp beta)),
      Function.Injective i ∧ (∀ v, TopSupport (i v)) ∧ (∀ v, (i v).1 2 = 0) := by
  letI : f.range.Normal := hH
  have hK := BinaryFourCanonicalTopBinaryQuotients.a4_binary_normal_le_klein f.range hbinary
  let k : Multiplicative V →* BinaryFourSymmetricKleinNormalCover.klein := {
    toFun v := ⟨SemidirectProduct.inl (f v),
      (BinaryFourSymmetricKleinNormalCover.inl_mem_klein _).mpr (hK ⟨v,rfl⟩)⟩
    map_one' := Subtype.ext (by simp)
    map_mul' v w := Subtype.ext (by simp) }
  let a : Multiplicative V →* Multiplicative SymmetricEnvelope :=
    BinaryFourCanonicalTopKleinEnvelope.kleinEmbedding.comp k
  have hk (r : R) (v : V) : k (Multiplicative.ofAdd (rho r v)) =
      MulAut.conjNormal (SemidirectProduct.inl (beta r)) (k (Multiplicative.ofAdd v)) := by
    apply Subtype.ext
    change SemidirectProduct.inl (f (Multiplicative.ofAdd (rho r v))) = _
    rw [hconj,map_mul,map_mul,map_inv]
    rfl
  let i : rho.IntertwiningMap
      (symmetricEnvelopeRepresentation.comp (SemidirectProduct.inl.comp beta)) := {
    toLinearMap := linearize a
    isIntertwining' r := by
      apply LinearMap.ext
      intro v
      change (BinaryFourCanonicalTopKleinEnvelope.kleinEmbedding
        (k (Multiplicative.ofAdd (rho r v)))).toAdd =
        symmetricEnvelopeRepresentation (SemidirectProduct.inl (beta r))
          (BinaryFourCanonicalTopKleinEnvelope.kleinEmbedding (k (Multiplicative.ofAdd v))).toAdd
      rw [hk]
      exact BinaryFourCanonicalTopKleinEnvelope.conjugate _ _ }
  have hkInj : Function.Injective k := by
    intro v w h
    apply hf
    exact congrArg (fun z : BinaryFourSymmetricKleinNormalCover.klein => z.1.left) h
  exact ⟨i,linearize_injective a
    (BinaryFourCanonicalTopKleinEnvelope.kleinEmbedding_injective.comp hkInj),
      (fun _ => ⟨rfl,rfl,rfl⟩),fun _ => rfl⟩

/-- A4 with nonzero actual denominator has no binary top contribution. -/
theorem a4_nonzero_top_intertwiner
    (N : Subgroup Complement) [N.Normal] (hN : N ≠ ⊥)
    (beta : R →* Complement) (rho : Representation Scalar R V)
    (f : Multiplicative V →* Complement ⧸ N) (hf : Function.Injective f)
    (hbinary : IsPGroup 2 f.range) :
    ∃ i : rho.IntertwiningMap
        (symmetricEnvelopeRepresentation.comp (SemidirectProduct.inl.comp beta)),
      Function.Injective i ∧ (∀ v, TopSupport (i v)) ∧ (∀ v, (i v).1 2 = 0) := by
  have hz := BinaryFourCanonicalTopBinaryQuotients.a4_nonzero_binary_eq_bot N hN f.range hbinary
  have hv (v : V) : v = 0 := by
    apply Multiplicative.ofAdd.injective
    apply hf
    have hm : f (Multiplicative.ofAdd v) ∈ f.range := ⟨_,rfl⟩
    rw [hz] at hm
    have he : f (Multiplicative.ofAdd v) = 1 := Subgroup.mem_bot.mp hm
    simpa only [show Multiplicative.ofAdd (0 : V)=1 from rfl,map_one] using he
  letI : Subsingleton V := ⟨fun v w => (hv v).trans (hv w).symm⟩
  refine ⟨0,fun _ _ _ => Subsingleton.elim _ _,?_,?_⟩
  · intro v
    exact ⟨rfl,rfl,rfl⟩
  · intro v
    rfl

end SymmetricSubgroupAsymptotics.BinaryFourCanonicalTopModuleEnvelope
end
