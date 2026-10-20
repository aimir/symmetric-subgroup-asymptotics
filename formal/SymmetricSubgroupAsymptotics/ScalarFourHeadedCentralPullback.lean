import SymmetricSubgroupAsymptotics.ScalarFourHeadDefinitions
import Mathlib.Algebra.Group.Subgroup.Ker

/-! Pull a pure scalar head back through an actual central binary kernel.
The same original kernel is retained as the headed central layer. No
character count, quotient census or source estimate is assumed. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.ScalarFourHeadedCentralPullback
variable {G H : Type} [Group G] [Group H]
  (h : ScalarFourHeadedQuotient H) (hz : h.center = ⊥)
  (q : G →* H) (hq : Function.Surjective q)
  (hcentral : ∀ z : q.ker, ∀ g : G, (z : G)*g=g*(z : G))
  (hbinary : IsPGroup 2 q.ker)

def top : G →* CyclicThree := h.top.comp q

def kernelMap : (top h q).ker →* h.top.ker :=
  (q.comp (top h q).ker.subtype).codRestrict h.top.ker (by intro p; exact p.2)

include hq in
theorem kernelMap_surjective : Function.Surjective (kernelMap h q) := by
  intro p
  obtain ⟨g,hg⟩ := hq (p : H)
  refine ⟨⟨g,?_⟩,?_⟩
  · change h.top (q g) = 1
    rw [hg]
    exact p.2
  · exact Subtype.ext hg

/-- Its centre is exactly the original kernel, expressed inside the
original index-three kernel rather than replaced by an abstract C2. -/
def centerEquiv : (kernelMap h q).ker ≃* q.ker :=
  MulEquiv.ofBijective
    ({
      toFun := fun z => ⟨((z : (top h q).ker) : G),
        congrArg Subtype.val (MonoidHom.mem_ker.mp z.2)⟩
      map_one' := rfl
      map_mul' := fun _ _ => rfl } : (kernelMap h q).ker →* q.ker)
    (by
      constructor
      · intro x y he
        apply Subtype.ext
        apply Subtype.ext
        exact congrArg (fun z : q.ker => (z : G)) he
      · intro z
        let p : (top h q).ker := ⟨z,by
          change h.top (q (z : G))=1
          rw [MonoidHom.mem_ker.mp z.2,map_one]⟩
        have hp : p ∈ (kernelMap h q).ker := by
          apply MonoidHom.mem_ker.mpr
          apply Subtype.ext
          exact MonoidHom.mem_ker.mp z.2
        exact ⟨⟨p,hp⟩,rfl⟩)

/-- Pure scalar coordinates survive the actual central pullback. -/
def headed : ScalarFourHeadedQuotient G where
  top := top h q
  top_surjective := h.top_surjective.comp hq
  center := (kernelMap h q).ker
  center_comm := by
    intro z hz' p
    apply Subtype.ext
    have hzq : ((z : (top h q).ker) : G) ∈ q.ker :=
      congrArg Subtype.val (MonoidHom.mem_ker.mp hz')
    exact hcentral ⟨((z : (top h q).ker) : G),hzq⟩ (p : G)
  center_twoGroup := hbinary.of_equiv (centerEquiv h q).symm
  layers := h.layers
  coord j := (h.coord j).comp (kernelMap h q)
  coord_center := by
    intro j z hz'
    change h.coord j (kernelMap h q z)=1
    rw [MonoidHom.mem_ker.mp hz',map_one]
  coord_joint := by
    intro p hp
    apply MonoidHom.mem_ker.mpr
    have hm := h.coord_joint (kernelMap h q p) hp
    rw [hz] at hm
    exact Subgroup.mem_bot.mp hm
  coord_twisted := by
    intro g p j
    change h.coord j (kernelMap h q (MulAut.conjNormal g p)) = _
    have he : kernelMap h q (MulAut.conjNormal g p) =
        MulAut.conjNormal (q g) (kernelMap h q p) := by
      apply Subtype.ext
      change q (g*(p : G)*g⁻¹) = q g*q (p : G)*(q g)⁻¹
      simp only [map_mul,map_inv]
    rw [he,h.coord_twisted]
    rfl
  coord_zero_surjective := (h.coord_zero_surjective).comp (kernelMap_surjective h q hq)

/-- The retained original centre contributes its actual binary size. -/
theorem weight_eq : (headed h hz q hq hcentral hbinary).weight =
    (h.layers+1)+Nat.log 2 (Nat.card q.ker) := by
  change (h.layers+1)+Nat.log 2 (Nat.card (kernelMap h q).ker) = _
  rw [Nat.card_congr (centerEquiv h q).toEquiv]

end SymmetricSubgroupAsymptotics.ScalarFourHeadedCentralPullback
end
