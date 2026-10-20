import SymmetricSubgroupAsymptotics.IrreducibleAbelianSemidirectNormalGenerators
import SymmetricSubgroupAsymptotics.NormalGeneratorTypeSharing

/-! An arbitrary subgroup of an abelian semidirect product retains a
positive normal-generator bound from its actual projection image when
that image acts faithfully and irreducibly. The retained translations
are either trivial or full. In the full case an actual lift is corrected
by a retained translation; no splitting of the original subgroup is
assumed. -/

set_option autoImplicit false
noncomputable section
open scoped Classical

namespace SymmetricSubgroupAsymptotics.IrreducibleAbelianSemidirectSubgroup

open SemidirectProduct

variable {V H : Type} [CommGroup V] [Group H]
  (φ : H →* MulAut V) (K : Subgroup (V ⋊[φ] H))

def projection : K →* H := (rightHom : V ⋊[φ] H →* H).comp K.subtype

abbrev Image := (projection φ K).range

def imageAction : Image φ K →* MulAut V :=
  φ.comp (projection φ K).range.subtype

def translations : Subgroup V := K.comap (inl : V →* V ⋊[φ] H)

/-- This map retains the actual left coordinate and merely restricts the
right coordinate to the actual projection image. -/
def actualMap : K →* (V ⋊[imageAction φ K] Image φ K) where
  toFun g := ⟨(g : V ⋊[φ] H).left, (projection φ K).rangeRestrict g⟩
  map_one' := by apply SemidirectProduct.ext <;> rfl
  map_mul' _ _ := by apply SemidirectProduct.ext <;> rfl

theorem actualMap_injective : Function.Injective (actualMap φ K) := by
  intro x y h
  apply Subtype.ext
  apply SemidirectProduct.ext
  · exact congrArg (fun z : V ⋊[imageAction φ K] Image φ K => z.left) h
  · exact congrArg (fun z : V ⋊[imageAction φ K] Image φ K => (z.right : H)) h

theorem conjugate_translation (g : V ⋊[φ] H) (v : V) :
    g * inl v * g⁻¹ = inl (φ g.right v) := by
  conv_lhs => rw [← inl_left_mul_inr_right g]
  have h : (inr g.right : V ⋊[φ] H) * inl v * (inr g.right)⁻¹ =
      inl (φ g.right v) := by
    rw [← map_inv]
    exact (inl_aut _ _).symm
  calc
    (inl g.left * inr g.right : V ⋊[φ] H) * inl v *
        (inl g.left * inr g.right)⁻¹ =
      (inl g.left : V ⋊[φ] H) *
        ((inr g.right : V ⋊[φ] H) * inl v * (inr g.right)⁻¹) *
          (inl g.left)⁻¹ := by group
    _ = (inl (g.left * φ g.right v * g.left⁻¹) : V ⋊[φ] H) := by
      rw [h, ← map_inv, ← map_mul, ← map_mul]
    _ = _ := by rw [mul_comm g.left, mul_inv_cancel_right]

theorem translations_invariant (h : Image φ K) (v : V)
    (hv : v ∈ translations φ K) : imageAction φ K h v ∈ translations φ K := by
  obtain ⟨g, hg⟩ := (projection φ K).rangeRestrict_surjective h
  have hr : (g : V ⋊[φ] H).right = (h : H) := congrArg Subtype.val hg
  change (inl (φ (h : H) v) : V ⋊[φ] H) ∈ K
  rw [← hr, ← conjugate_translation]
  exact K.mul_mem (K.mul_mem g.property hv) (K.inv_mem g.property)

theorem translations_eq_bot_or_top
    (hirr : IrreducibleAbelianSemidirect.Irreducible (imageAction φ K)) :
    translations φ K = ⊥ ∨ translations φ K = ⊤ :=
  hirr (translations φ K) (translations_invariant φ K)

theorem projection_injective_of_translations_bot
    (hbot : translations φ K = ⊥) : Function.Injective (projection φ K) := by
  apply (MonoidHom.ker_eq_bot_iff _).mp
  apply le_antisymm _ bot_le
  intro g hg
  have hr : (g : V ⋊[φ] H).right = 1 := MonoidHom.mem_ker.mp hg
  have he : (inl (g : V ⋊[φ] H).left : V ⋊[φ] H) = (g : V ⋊[φ] H) :=
    SemidirectProduct.ext rfl hr.symm
  have hv : (g : V ⋊[φ] H).left ∈ translations φ K := by
    change (inl (g : V ⋊[φ] H).left : V ⋊[φ] H) ∈ K
    rw [he]
    exact g.property
  have hl : (g : V ⋊[φ] H).left = 1 := Subgroup.mem_bot.mp (hbot ▸ hv)
  apply Subgroup.mem_bot.mpr
  apply Subtype.ext
  exact SemidirectProduct.ext hl hr

def projectionEquiv (hbot : translations φ K = ⊥) : K ≃* Image φ K :=
  MulEquiv.ofBijective (projection φ K).rangeRestrict
    ⟨fun _ _ h => projection_injective_of_translations_bot φ K hbot
      (congrArg Subtype.val h), (projection φ K).rangeRestrict_surjective⟩

/-- Surjectivity is proved by translating an actual lift with the prescribed
projection. It does not require a pure complement element in the subgroup. -/
theorem actualMap_surjective_of_translations_top
    (htop : translations φ K = ⊤) : Function.Surjective (actualMap φ K) := by
  intro y
  obtain ⟨x, hx⟩ := (projection φ K).rangeRestrict_surjective y.right
  let v : V := y.left * (x : V ⋊[φ] H).left⁻¹
  have hv : v ∈ translations φ K := by rw [htop]; exact Subgroup.mem_top v
  let z : K := ⟨inl v * (x : V ⋊[φ] H), K.mul_mem hv x.property⟩
  refine ⟨z, ?_⟩
  apply SemidirectProduct.ext
  · change (inl v * (x : V ⋊[φ] H)).left = y.left
    simp [v]
  · apply Subtype.ext
    change (inl v * (x : V ⋊[φ] H)).right = (y.right : H)
    simpa only [mul_right, right_inl, one_mul] using congrArg Subtype.val hx

def actualEquiv (htop : translations φ K = ⊤) :
    K ≃* (V ⋊[imageAction φ K] Image φ K) :=
  MulEquiv.ofBijective (actualMap φ K)
    ⟨actualMap_injective φ K, actualMap_surjective_of_translations_top φ K htop⟩

/-- A positive uniform bound for normal subgroups of the actual image
passes unchanged to the original affine subgroup. -/
theorem normal_generating_tuples [Nontrivial V]
    (hfaith : Function.Injective (imageAction φ K))
    (hirr : IrreducibleAbelianSemidirect.Irreducible (imageAction φ K))
    {t : ℕ} (ht : 0 < t)
    (himage : ∀ N : Subgroup (Image φ K), N.Normal →
      ∃ x : Fin t → Image φ K, Subgroup.normalClosure (Set.range x) = N) :
    ∀ N : Subgroup K, N.Normal →
      ∃ x : Fin t → K, Subgroup.normalClosure (Set.range x) = N := by
  rcases translations_eq_bot_or_top φ K hirr with hbot | htop
  · let e := projectionEquiv φ K hbot
    exact normal_generating_tuples_of_surjective e.symm.toMonoidHom
      e.symm.surjective himage
  · let e := actualEquiv φ K htop
    exact normal_generating_tuples_of_surjective e.symm.toMonoidHom
      e.symm.surjective
      (IrreducibleAbelianSemidirect.normal_generating_tuples
        (imageAction φ K) hfaith hirr ht himage)

theorem normalGen_le [Nontrivial V]
    (hfaith : Function.Injective (imageAction φ K))
    (hirr : IrreducibleAbelianSemidirect.Irreducible (imageAction φ K))
    {t : ℕ} (ht : 0 < t)
    (himage : ∀ N : Subgroup (Image φ K), N.Normal →
      ∃ x : Fin t → Image φ K, Subgroup.normalClosure (Set.range x) = N)
    (N : Subgroup K) (hN : N.Normal) : MarkedC4.normalGen N ≤ t := by
  letI := hN
  obtain ⟨x, hx⟩ := normal_generating_tuples φ K hfaith hirr ht himage N hN
  exact normalGen_le_of_fin_tuple x hx

theorem quotientSocle [Nontrivial V]
    (hfaith : Function.Injective (imageAction φ K))
    (hirr : IrreducibleAbelianSemidirect.Irreducible (imageAction φ K))
    {t : ℕ} (ht : 0 < t)
    (himage : ∀ M : Subgroup (Image φ K), M.Normal →
      ∃ x : Fin t → Image φ K, Subgroup.normalClosure (Set.range x) = M)
    (N : Subgroup K) [N.Normal] : SocleNormalGeneratorBound (K ⧸ N) t :=
  quotientSocleNormalGeneratorBound_of_normal_generating_tuples
    (normal_generating_tuples φ K hfaith hirr ht himage) N

end SymmetricSubgroupAsymptotics.IrreducibleAbelianSemidirectSubgroup

end
