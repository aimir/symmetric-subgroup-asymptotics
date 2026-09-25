import SymmetricSubgroupAsymptotics.ImprimitiveChiefCoordinates

/-! Literal quotient coordinates on adjacent original chief intersections.
All conjugated coordinates descend through the exact preceding intersection,
and jointly separate the actual ambient section. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace SymmetricSubgroupAsymptotics
variable {A R : Type} [Group A] [Group R]
variable (N : Subgroup A) [N.Normal] (θ : N→*R)
variable (B L : Subgroup R) [B.Normal] [L.Normal]

abbrev localChiefSourceSection :=
  normalChainQuotient (localChiefIntersection N θ B) (localChiefIntersection N θ L)

def localChiefRawQuotientCoordinate (a:A) :
    localChiefIntersection N θ L →* normalChainQuotient B L :=
  ((normalChainMap B L).comp (localChiefIntersectionCoordinate N θ L)).comp
    (MulAut.conjNormal a).toMonoidHom

omit [L.Normal] in
theorem localChiefRawQuotientCoordinate_kernel (a:A)
    (c:localChiefIntersection N θ L) :
    localChiefRawQuotientCoordinate N θ B L a c=1 ↔
      θ (MulAut.conjNormal a
        (⟨(c:A),localChiefIntersection_le N θ L c.2⟩:N))∈B := by
  change (⟨QuotientGroup.mk' B _,_⟩:normalChainQuotient B L)=1 ↔ _
  rw [Subtype.ext_iff]
  exact QuotientGroup.eq_one_iff _

omit [L.Normal] in
theorem localChiefRawQuotientCoordinate_ker_le (a:A) :
    (normalChainMap (localChiefIntersection N θ B) (localChiefIntersection N θ L)).ker ≤
      (localChiefRawQuotientCoordinate N θ B L a).ker := by
  intro c hc
  have hx : (c:A)∈localChiefIntersection N θ B :=
    (QuotientGroup.eq_one_iff _).mp (congrArg Subtype.val hc)
  apply (localChiefRawQuotientCoordinate_kernel N θ B L a c).mpr
  exact (mem_localChiefIntersection N θ B
    ⟨(c:A),localChiefIntersection_le N θ L c.2⟩).mp hx a

def localChiefQuotientCoordinate (a:A) :
    localChiefSourceSection N θ B L →* normalChainQuotient B L :=
  (normalChainMap (localChiefIntersection N θ B) (localChiefIntersection N θ L)).liftOfSurjective
    (normalChainMap_surjective _ _)
    ⟨localChiefRawQuotientCoordinate N θ B L a,
      localChiefRawQuotientCoordinate_ker_le N θ B L a⟩

theorem localChiefQuotientCoordinate_apply (a:A) (c:localChiefIntersection N θ L) :
    localChiefQuotientCoordinate N θ B L a
      (normalChainMap (localChiefIntersection N θ B) (localChiefIntersection N θ L) c)=
      localChiefRawQuotientCoordinate N θ B L a c :=
  MonoidHom.liftOfRightInverse_comp_apply _ _ _ _ _

theorem localChiefQuotientCoordinates_separate :
    Function.Injective (fun c:localChiefSourceSection N θ B L =>
      fun a:A=>localChiefQuotientCoordinate N θ B L a c) := by
  intro x y hxy
  apply mul_inv_eq_one.mp
  obtain ⟨c,hc⟩ := normalChainMap_surjective
    (localChiefIntersection N θ B) (localChiefIntersection N θ L) (x*y⁻¹)
  rw [←hc]
  apply Subtype.ext
  apply (QuotientGroup.eq_one_iff _).mpr
  apply (mem_localChiefIntersection N θ B
    ⟨(c:A),localChiefIntersection_le N θ L c.2⟩).mpr
  intro a
  apply (localChiefRawQuotientCoordinate_kernel N θ B L a c).mp
  rw [←localChiefQuotientCoordinate_apply,hc,map_mul,map_inv]
  exact mul_inv_eq_one.mpr (congrFun hxy a)

theorem localChiefQuotientCoordinate_range (a:A) :
    (localChiefQuotientCoordinate N θ B L a).range=
      ((normalChainMap B L).comp (localChiefIntersectionCoordinate N θ L)).range := by
  let τ := normalChainMap (localChiefIntersection N θ B) (localChiefIntersection N θ L)
  have ht : Function.Surjective τ := normalChainMap_surjective _ _
  have he : (localChiefQuotientCoordinate N θ B L a).comp τ=
      localChiefRawQuotientCoordinate N θ B L a :=
    MonoidHom.ext (localChiefQuotientCoordinate_apply N θ B L a)
  have hr := congrArg MonoidHom.range he
  rw [MonoidHom.range_comp,MonoidHom.range_eq_top.mpr ht,←MonoidHom.range_eq_map] at hr
  rw [hr]
  unfold localChiefRawQuotientCoordinate
  have ha : ((MulAut.conjNormal (H:=localChiefIntersection N θ L) a).toMonoidHom).range=⊤ :=
    MonoidHom.range_eq_top.mpr (MulAut.conjNormal (H:=localChiefIntersection N θ L) a).surjective
  rw [MonoidHom.range_comp,ha,←MonoidHom.range_eq_map]

section NormalImage
variable (H : Subgroup A) (β : H→*R)
variable (hθ : ∀ (h:H) (n:N),θ (MulAut.conjNormal (h:A) n)=β h*θ n*(β h)⁻¹)
variable (hβ : Function.Surjective β)
include hθ hβ

theorem localChiefQuotientCoordinate_image_normal (a:A) :
    ((localChiefQuotientCoordinate N θ B L a).range.map
      (normalChainQuotient B L).subtype).Normal := by
  rw [localChiefQuotientCoordinate_range]
  constructor
  intro x hx r
  obtain ⟨z,hz,rfl⟩ := hx
  obtain ⟨c,rfl⟩ := hz
  obtain ⟨s,rfl⟩ := QuotientGroup.mk'_surjective B r
  obtain ⟨h,rfl⟩ := hβ s
  refine ⟨(normalChainMap B L)
    (localChiefIntersectionCoordinate N θ L (MulAut.conjNormal (h:A) c)),
    ⟨MulAut.conjNormal (h:A) c,rfl⟩,?_⟩
  change QuotientGroup.mk' B
    (θ (MulAut.conjNormal (h:A)
      (⟨(c:A),localChiefIntersection_le N θ L c.2⟩:N)))=_
  rw [hθ,map_mul,map_mul,map_inv]
  rfl

end NormalImage
end SymmetricSubgroupAsymptotics
