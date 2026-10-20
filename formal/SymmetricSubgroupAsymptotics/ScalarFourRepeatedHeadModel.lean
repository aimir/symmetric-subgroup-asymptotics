import SymmetricSubgroupAsymptotics.ScalarFourDoubleHeadCentralProduct
import SymmetricSubgroupAsymptotics.NaturalA4ScalarFourHead

/-! The repeated scalar head as the literal fiber product A4 ×_C3 A4.
Its two Klein coordinates share the same actual C3 top. -/
set_option autoImplicit false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics
namespace ScalarFourRepeatedHeadModel

private abbrev A := NaturalA4ScalarFourHead.G
private abbrev t := NaturalA4ScalarFourHead.top

def model : Subgroup (A × A) where
  carrier := {p | t p.1 = t p.2}
  one_mem' := by simp
  mul_mem' := by
    intro p q hp hq
    change t (p.1 * q.1) = t (p.2 * q.2)
    rw [map_mul, map_mul, hp, hq]
  inv_mem' := by
    intro p hp
    change t p.1⁻¹ = t p.2⁻¹
    rw [map_inv, map_inv, hp]

abbrev G := model

def top : G →* CyclicThree := t.comp ((MonoidHom.fst A A).comp model.subtype)

def leftKernel : top.ker →* t.ker :=
  ((MonoidHom.fst A A).comp (model.subtype.comp top.ker.subtype)).codRestrict
    t.ker (by intro p; exact p.2)

def rightKernel : top.ker →* t.ker :=
  ((MonoidHom.snd A A).comp (model.subtype.comp top.ker.subtype)).codRestrict
    t.ker (by
      intro p
      change t (p : G).1.2 = 1
      rw [← (p : G).2]
      exact p.2)

def coord (k : Fin 2) : top.ker →* ScalarFour :=
  NaturalA4ScalarFourHead.coord.comp (if k = 0 then leftKernel else rightKernel)

theorem coord_joint : Function.Injective (fun p : top.ker => (coord 0 p, coord 1 p)) := by
  intro p q he
  have hl : leftKernel p = leftKernel q :=
    NaturalA4ScalarFourHead.coord_bijective.injective (congrArg Prod.fst he)
  have hr : rightKernel p = rightKernel q :=
    NaturalA4ScalarFourHead.coord_bijective.injective (congrArg Prod.snd he)
  apply Subtype.ext
  apply Subtype.ext
  exact Prod.ext (congrArg Subtype.val hl) (congrArg Subtype.val hr)

def headed : ScalarFourHeadedQuotient G where
  top := top
  top_surjective := by
    intro c
    obtain ⟨q,hq⟩ := NaturalA4ScalarFourHead.top_surjective c
    exact ⟨⟨(q,q),rfl⟩,hq⟩
  center := ⊥
  center_comm := by simp
  center_twoGroup := IsPGroup.of_bot
  layers := 1
  coord := coord
  coord_center := by simp
  coord_joint := by
    intro p hp
    rw [Subgroup.mem_bot]
    apply coord_joint
    exact Prod.ext (by simpa using hp 0) (by simpa using hp 1)
  coord_twisted := by
    intro q p k
    fin_cases k
    · have he : leftKernel (MulAut.conjNormal q p) =
          MulAut.conjNormal q.1.1 (leftKernel p) := by
        apply Subtype.ext
        rfl
      change NaturalA4ScalarFourHead.coord
        (leftKernel (MulAut.conjNormal q p)) = _
      rw [he]
      exact NaturalA4ScalarFourHead.headed.coord_twisted q.1.1 (leftKernel p) 0
    · have he : rightKernel (MulAut.conjNormal q p) =
          MulAut.conjNormal q.1.2 (rightKernel p) := by
        apply Subtype.ext
        rfl
      change NaturalA4ScalarFourHead.coord
        (rightKernel (MulAut.conjNormal q p)) = _
      rw [he]
      have ht : t q.1.1 = t q.1.2 := q.2
      simpa only [top, MonoidHom.comp_apply, MonoidHom.coe_fst,
        Subgroup.coe_subtype, ht] using
        NaturalA4ScalarFourHead.headed.coord_twisted q.1.2 (rightKernel p) 0
  coord_zero_surjective := by
    intro v
    obtain ⟨p,hp⟩ := NaturalA4ScalarFourHead.coord_surjective v
    let q : G := ⟨((p : A),1),by
      change t (p : A)=t 1
      rw [map_one]
      exact MonoidHom.mem_ker.mp p.2⟩
    have hq : q ∈ top.ker := p.2
    exact ⟨⟨q,hq⟩,hp⟩

end ScalarFourRepeatedHeadModel
end SymmetricSubgroupAsymptotics
end
