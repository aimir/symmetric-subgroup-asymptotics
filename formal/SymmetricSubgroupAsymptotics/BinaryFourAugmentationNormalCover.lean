import SymmetricSubgroupAsymptotics.BinaryFourAugmentationActions
import SymmetricSubgroupAsymptotics.NormalCoverQuotientSocles

/-! The actual diagonal translation subgroup is the unique minimal
normal subgroup of both augmentation models. The proof uses faithful
translation centralizers and the displayed two-step unipotent action. -/

set_option autoImplicit false
noncomputable section
open scoped Classical

namespace SymmetricSubgroupAsymptotics
namespace BinaryFourBlockAugmentation

open SemidirectProduct

def diagonalCoordinates (d : Local) : Coordinates := ![d 0, d 1, 0, 0, 0, 0]

def diagonalVector (full : Bool) (d : Local) : space full :=
  ⟨diagonalCoordinates d, by intro h; rfl⟩

def diagonalHom (full : Bool) : Klein →* Model full where
  toFun d := inl (Multiplicative.ofAdd (diagonalVector full d.toAdd))
  map_one' := by
    apply SemidirectProduct.ext
    · apply Multiplicative.toAdd.injective
      apply Subtype.ext
      ext i
      fin_cases i <;> rfl
    · rfl
  map_mul' d e := by
    rw [← map_mul]
    congr 1
    apply Multiplicative.toAdd.injective
    apply Subtype.ext
    ext i
    fin_cases i <;> simp [diagonalVector, diagonalCoordinates]

theorem diagonalHom_injective (full : Bool) : Function.Injective (diagonalHom full) := by
  intro d e h
  apply Multiplicative.toAdd.injective
  ext i
  fin_cases i
  · exact congrArg (fun g : Model full => (g.left.toAdd : Coordinates) 0) h
  · exact congrArg (fun g : Model full => (g.left.toAdd : Coordinates) 1) h

def diagonalSubgroup (full : Bool) : Subgroup (Model full) := (diagonalHom full).range

theorem diagonalSubgroup_ne_bot (full : Bool) : diagonalSubgroup full ≠ ⊥ := by
  intro h
  have hm : diagonalHom full (Multiplicative.ofAdd ![1, 0]) ∈ diagonalSubgroup full :=
    ⟨_, rfl⟩
  have he := diagonalHom_injective full
    ((Subgroup.mem_bot.mp (h ▸ hm)).trans (diagonalHom full).map_one.symm)
  have hv := congrArg (fun d : Klein => d.toAdd 0) he
  exact one_ne_zero hv

def modelTranslations (full : Bool) : Subgroup (Model full) :=
  (inl : Multiplicative (space full) →* Model full).range

instance modelTranslations_normal (full : Bool) : (modelTranslations full).Normal := by
  rw [modelTranslations, range_inl_eq_ker_rightHom]
  infer_instance

theorem model_conj_inl (full : Bool) (g : Model full)
    (x : Multiplicative (space full)) :
    g * inl x * g⁻¹ = inl (action full g.right x) := by
  conv_lhs => rw [← inl_left_mul_inr_right g]
  have h : (inr g.right : Model full) * inl x * (inr g.right)⁻¹ =
      inl (action full g.right x) := by
    rw [← map_inv]
    exact (inl_aut (φ := action full) g.right x).symm
  calc
    (inl g.left * inr g.right : Model full) * inl x *
        (inl g.left * inr g.right)⁻¹ =
        inl g.left * ((inr g.right : Model full) * inl x * (inr g.right)⁻¹) *
          (inl g.left)⁻¹ := by group
    _ = inl (g.left * action full g.right x * g.left⁻¹) := by
      rw [h, ← map_inv, ← map_mul, ← map_mul]
    _ = _ := by rw [mul_comm g.left, mul_inv_cancel_right]

theorem diagonal_conjugate (full : Bool) (g : Model full) (d : Klein) :
    g * diagonalHom full d * g⁻¹ =
      diagonalHom full (kleinCyclicAction g.right.right d) := by
  change g * inl (Multiplicative.ofAdd (diagonalVector full d.toAdd)) * g⁻¹ =
    inl (Multiplicative.ofAdd
      (diagonalVector full (kleinCyclicAction g.right.right d).toAdd))
  rw [model_conj_inl]
  congr 1
  apply Multiplicative.toAdd.injective
  apply Subtype.ext
  change complementLinear g.right (diagonalCoordinates d.toAdd) =
    diagonalCoordinates ((kleinCyclicAction g.right.right d).toAdd)
  have hcoord : ∀ (p : Klein) (z : Ternary) (a : Klein),
      complementLinear ⟨p, z⟩ (diagonalCoordinates a.toAdd) =
        diagonalCoordinates ((kleinCyclicAction z a).toAdd) := by decide +kernel
  exact hcoord g.right.left g.right.right d

instance diagonalSubgroup_normal (full : Bool) : (diagonalSubgroup full).Normal where
  conj_mem g hg h := by
    obtain ⟨d, rfl⟩ := hg
    exact ⟨kleinCyclicAction h.right.right d, (diagonal_conjugate full h d).symm⟩

private theorem translation_inter_ne_bot (full : Bool)
    (N : Subgroup (Model full)) (hN : N.Normal) (hNb : N ≠ ⊥) :
    N ⊓ modelTranslations full ≠ ⊥ := by
  intro hbot
  apply hNb
  have hNT : N ≤ modelTranslations full := by
    intro x hx
    have hc : x ∈ Subgroup.centralizer
        (modelTranslations full : Set (Model full)) := by
      rw [Subgroup.mem_centralizer_iff]
      intro v hv
      have hcomm : x * v * x⁻¹ * v⁻¹ ∈ N ⊓ modelTranslations full := by
        refine ⟨?_, (modelTranslations full).mul_mem
          ((modelTranslations_normal full).conj_mem v hv x)
          ((modelTranslations full).inv_mem hv)⟩
        have hi := hN.conj_mem x⁻¹ (N.inv_mem hx) v
        simpa only [mul_assoc] using N.mul_mem hx hi
      have he : x * v * x⁻¹ * v⁻¹ = 1 :=
        Subgroup.mem_bot.mp (hbot ▸ hcomm)
      calc
        v * x = (x * v * x⁻¹ * v⁻¹) * (v * x) := by rw [he, one_mul]
        _ = x * v := by group
    have ha := (SemidirectAbelianCentralizer.mem_centralizer_iff
      (action full) x).mp hc
    have hr : x.right = 1 :=
      action_injective full (ha.trans (action full).map_one.symm)
    rw [modelTranslations, range_inl_eq_ker_rightHom, MonoidHom.mem_ker]
    exact hr
  apply le_antisymm _ bot_le
  intro x hx
  exact hbot ▸ (show x ∈ N ⊓ modelTranslations full from ⟨hx, hNT hx⟩)

/-- Every nonzero coordinate vector either is diagonal, or one of its
two displayed Klein differences is a nonzero diagonal vector. -/
theorem nonzero_diagonal_reduction (x : Coordinates) (hx : x ≠ 0) :
    ∃ d : Local, d ≠ 0 ∧
      (x = diagonalCoordinates d ∨
       u x + x = diagonalCoordinates d ∨
       v x + x = diagonalCoordinates d) := by
  revert x
  decide +kernel

theorem diagonal_orbit (d : Local) (hd : d ≠ 0) (e : Local) :
    e = 0 ∨ e = d ∨ e = localCycle d ∨ e = localCycle (localCycle d) := by
  revert d e
  decide +kernel

theorem normal_cover (full : Bool) (N : Subgroup (Model full))
    (hN : N.Normal) (hNb : N ≠ ⊥) : diagonalSubgroup full ≤ N := by
  obtain ⟨g, hg, hg1⟩ := (N ⊓ modelTranslations full).bot_or_exists_ne_one.resolve_left
    (translation_inter_ne_bot full N hN hNb)
  obtain ⟨x, hx⟩ := hg.2
  have hxN : (inl x : Model full) ∈ N := hx.symm ▸ hg.1
  have hx0 : (x.toAdd : Coordinates) ≠ 0 := by
    intro h
    apply hg1
    rw [← hx]
    have hx1 : x = 1 := Multiplicative.toAdd.injective (Subtype.ext h)
    rw [hx1, map_one]
  obtain ⟨d, hd, hdcase⟩ := nonzero_diagonal_reduction x.toAdd hx0
  have hdN : diagonalHom full (Multiplicative.ofAdd d) ∈ N := by
    rcases hdcase with he | he | he
    · have hxe : (inl x : Model full) = diagonalHom full (Multiplicative.ofAdd d) := by
        change inl x = inl (Multiplicative.ofAdd (diagonalVector full d))
        congr 1
        apply Multiplicative.toAdd.injective
        exact Subtype.ext he
      exact hxe ▸ hxN
    · have hm := N.mul_mem (hN.conj_mem (inl x) hxN (inr uElement)) hxN
      rw [model_conj_inl, ← map_mul] at hm
      change (inl (action full uElement x * x) : Model full) ∈ N at hm
      have hxe : action full uElement x * x =
          Multiplicative.ofAdd (diagonalVector full d) := by
        apply Multiplicative.toAdd.injective
        apply Subtype.ext
        change complementLinear uElement (x.toAdd : Coordinates) + x.toAdd = _
        rw [linear_u]
        exact he
      rw [hxe] at hm
      exact hm
    · have hm := N.mul_mem (hN.conj_mem (inl x) hxN (inr vElement)) hxN
      rw [model_conj_inl, ← map_mul] at hm
      change (inl (action full vElement x * x) : Model full) ∈ N at hm
      have hxe : action full vElement x * x =
          Multiplicative.ofAdd (diagonalVector full d) := by
        apply Multiplicative.toAdd.injective
        apply Subtype.ext
        change complementLinear vElement (x.toAdd : Coordinates) + x.toAdd = _
        rw [linear_v]
        exact he
      rw [hxe] at hm
      exact hm
  have hcN (a : Local) (ha : diagonalHom full (Multiplicative.ofAdd a) ∈ N) :
      diagonalHom full (Multiplicative.ofAdd (localCycle a)) ∈ N := by
    have hh := hN.conj_mem _ ha (inr cElement)
    rw [diagonal_conjugate] at hh
    change diagonalHom full (kleinCyclicAction cElement.right (Multiplicative.ofAdd a)) ∈ N at hh
    have he : ∀ b : Local, kleinCyclicAction cElement.right (Multiplicative.ofAdd b) =
        Multiplicative.ofAdd (localCycle b) := by decide +kernel
    rw [he] at hh
    exact hh
  rintro y ⟨e, rfl⟩
  rcases diagonal_orbit d hd e.toAdd with he | he | he | he
  · have he1 : e = 1 := Multiplicative.toAdd.injective he
    rw [he1, map_one]
    exact N.one_mem
  · have he1 : e = Multiplicative.ofAdd d := Multiplicative.toAdd.injective he
    rw [he1]
    exact hdN
  · have he1 : e = Multiplicative.ofAdd (localCycle d) := Multiplicative.toAdd.injective he
    rw [he1]
    exact hcN d hdN
  · have he1 : e = Multiplicative.ofAdd (localCycle (localCycle d)) :=
      Multiplicative.toAdd.injective he
    rw [he1]
    exact hcN (localCycle d) (hcN d hdN)

end BinaryFourBlockAugmentation
end SymmetricSubgroupAsymptotics

end
