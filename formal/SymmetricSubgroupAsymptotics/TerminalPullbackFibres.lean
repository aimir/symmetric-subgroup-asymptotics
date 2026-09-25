import SymmetricSubgroupAsymptotics.TerminalIncidencePullback

/-!
# Original image fibres and literal terminal pullbacks

An injective record on the complete exterior identifies its original image
fibre with the full-image subgroups of the literal pullback. No subgroup or
extension is replaced by another group having only the same order.
-/

set_option autoImplicit false
noncomputable section

namespace SymmetricSubgroupAsymptotics

variable {X V G T : Type} [Group X] [Group V] [Group G] [Group T]

/-- The original product quotient, including the entire exterior. -/
def terminalProductImageMap (π : X →* V) : X × T →* V × T :=
  π.prodMap (MonoidHom.id T)

/-- The original-coordinate map out of the literal pullback. -/
def terminalPullbackEmbedding (π : X →* V) (j : G →* V × T) :
    terminalPullbackGroup π ((MonoidHom.fst V T).comp j) →* X × T :=
  (MonoidHom.fst X G).comp (terminalPullbackGroup π
    ((MonoidHom.fst V T).comp j)).subtype |>.prod
      (((MonoidHom.snd V T).comp j).comp
        (terminalPullbackProjection π ((MonoidHom.fst V T).comp j)))

@[simp] theorem terminalPullbackEmbedding_apply (π : X →* V) (j : G →* V × T)
    (x : terminalPullbackGroup π ((MonoidHom.fst V T).comp j)) :
    terminalPullbackEmbedding π j x = (x.1.1,(j x.1.2).2) := rfl

/-- The square commutes in the actual original product. -/
theorem terminalPullbackEmbedding_commutes (π : X →* V) (j : G →* V × T) :
    (terminalProductImageMap (T := T) π).comp (terminalPullbackEmbedding π j) =
      j.comp (terminalPullbackProjection π ((MonoidHom.fst V T).comp j)) := by
  ext x
  · exact x.2
  · rfl

theorem terminalPullbackEmbedding_injective (π : X →* V) (j : G →* V × T)
    (hj : Function.Injective j) : Function.Injective (terminalPullbackEmbedding π j) := by
  intro x y h
  change (x.1.1,(j x.1.2).2) = (y.1.1,(j y.1.2).2) at h
  have hfst : x.1.1 = y.1.1 := congrArg (fun z : X × T => z.1) h
  have hsnd : (j x.1.2).2 = (j y.1.2).2 := congrArg (fun z : X × T => z.2) h
  apply Subtype.ext
  apply Prod.ext hfst
  apply hj
  apply Prod.ext _ hsnd
  calc
    (j x.1.2).1 = π x.1.1 := x.2.symm
    _ = π y.1.1 := congrArg π hfst
    _ = (j y.1.2).1 := y.2

/-- Every original point above the record image has a literal pullback
preimage. No surjectivity of the original extension is needed here. -/
theorem terminalPullbackEmbedding_range (π : X →* V) (j : G →* V × T) :
    (terminalPullbackEmbedding π j).range =
      j.range.comap (terminalProductImageMap (T := T) π) := by
  ext x
  constructor
  · rintro ⟨y,rfl⟩
    exact ⟨y.1.2,Prod.ext y.2.symm rfl⟩
  · rintro ⟨g,hg⟩
    refine ⟨⟨(x.1,g),?_⟩,?_⟩
    · exact (congrArg Prod.fst hg).symm
    · change (x.1,(j g).2) = x
      apply Prod.ext
      · rfl
      · exact congrArg (fun z : V × T => z.2) hg

/-- Exact original subgroup fibres are equivalent to the full-image
subgroups of the literal pullback through an injective record. -/
def terminalPullbackImageFibreEquiv (π : X →* V) (j : G →* V × T)
    (hj : Function.Injective j) :
    {H : Subgroup (X × T) // H.map (terminalProductImageMap (T := T) π) = j.range} ≃
      {L : Subgroup (terminalPullbackGroup π ((MonoidHom.fst V T).comp j)) //
        L.map (terminalPullbackProjection π ((MonoidHom.fst V T).comp j)) = ⊤} where
  toFun H := ⟨H.1.comap (terminalPullbackEmbedding π j),by
    apply top_unique
    intro g _
    have hg : j g ∈ H.1.map (terminalProductImageMap (T := T) π) := by
      rw [H.2]
      exact ⟨g,rfl⟩
    obtain ⟨x,hx,he⟩ := Subgroup.mem_map.mp hg
    let y : terminalPullbackGroup π ((MonoidHom.fst V T).comp j) :=
      ⟨(x.1,g),congrArg Prod.fst he⟩
    refine Subgroup.mem_map.mpr ⟨y,?_,rfl⟩
    change (x.1,(j g).2) ∈ H.1
    have hs : x.2 = (j g).2 := congrArg Prod.snd he
    simpa only [← hs] using hx⟩
  invFun L := ⟨L.1.map (terminalPullbackEmbedding π j),by
    rw [Subgroup.map_map,terminalPullbackEmbedding_commutes,← Subgroup.map_map,L.2,
      ← MonoidHom.range_eq_map]⟩
  left_inv H := by
    apply Subtype.ext
    apply Subgroup.map_comap_eq_self
    rw [terminalPullbackEmbedding_range]
    intro x hx
    change terminalProductImageMap π x ∈ j.range
    rw [← H.2]
    exact Subgroup.mem_map.mpr ⟨x,hx,rfl⟩
  right_inv L := Subtype.ext (Subgroup.comap_map_eq_self_of_injective
    (terminalPullbackEmbedding_injective π j hj) L.1)

/-- Literal fibre counts agree before any positive enlargement or outer
weight is applied. -/
theorem terminalPullbackImageFibre_card (π : X →* V) (j : G →* V × T)
    (hj : Function.Injective j) :
    Nat.card {H : Subgroup (X × T) //
      H.map (terminalProductImageMap (T := T) π) = j.range} =
      Nat.card {L : Subgroup (terminalPullbackGroup π ((MonoidHom.fst V T).comp j)) //
        L.map (terminalPullbackProjection π ((MonoidHom.fst V T).comp j)) = ⊤} :=
  Nat.card_congr (terminalPullbackImageFibreEquiv π j hj)

/-- Centrality of the original kernel passes to the literal pullback. -/
theorem terminalPullbackProjection_ker_central (π : X →* V) (f : G →* V)
    (hc : π.ker ≤ Subgroup.center X) :
    (terminalPullbackProjection π f).ker ≤ Subgroup.center (terminalPullbackGroup π f) := by
  intro z hz
  have hzG : z.1.2 = 1 := hz
  have hzX : π z.1.1 = 1 := by
    have h := z.2
    change π z.1.1 = f z.1.2 at h
    simpa only [hzG,map_one] using h
  apply Subgroup.mem_center_iff.mpr
  intro x
  apply Subtype.ext
  apply Prod.ext
  · exact Subgroup.mem_center_iff.mp (hc hzX) x.1.1
  · change x.1.2 * z.1.2 = z.1.2 * x.1.2
    rw [hzG,mul_one,one_mul]

end SymmetricSubgroupAsymptotics
