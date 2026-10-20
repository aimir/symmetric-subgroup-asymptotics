import SymmetricSubgroupAsymptotics.ScalarFourDoubleHeadJointCount

/-! A concrete central product construction for the joint count interface.
The central factor is retained through two jointly injective binary maps;
zero maps allow central rank zero or one. -/
set_option autoImplicit false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics
namespace ScalarFourDoubleHeadCentralProduct

variable {H B : Type} [Group H] [CommGroup B]
  (h : ScalarFourHeadedQuotient H)
  (i j : Fin (h.layers + 1))
  (hjoint : Function.Injective (fun p => (h.coord i p, h.coord j p)))
  (b : Fin 2 → (B →* Multiplicative (ZMod 2)))
  (bjoint : Function.Injective (fun z => (b 0 z, b 1 z)))
  (hB : IsPGroup 2 B)

def top : H × B →* CyclicThree := h.top.comp (MonoidHom.fst H B)

def firstKernel : (top h (B := B)).ker →* h.top.ker :=
  ((MonoidHom.fst H B).comp (top h (B := B)).ker.subtype).codRestrict
    h.top.ker (by intro p; exact p.2)

def centralKernel : (top h (B := B)).ker →* B :=
  (MonoidHom.snd H B).comp (top h (B := B)).ker.subtype

private theorem firstKernel_conj (q : H × B) (p : (top h (B := B)).ker) :
    firstKernel h (MulAut.conjNormal q p) =
      MulAut.conjNormal q.1 (firstKernel h p) := by
  apply Subtype.ext
  rfl

private theorem centralKernel_conj (q : H × B) (p : (top h (B := B)).ker) :
    centralKernel h (MulAut.conjNormal q p) = centralKernel h p := by
  change q.2 * (p : H × B).2 * q.2⁻¹ = (p : H × B).2
  simp [mul_comm, mul_left_comm]

/-- The scalar kernel together with the retained central coordinates gives
an actual headed quotient; no character or source bound is an input. -/
def headed : ScalarFourHeadedQuotient (H × B) where
  top := top h
  top_surjective := by
    intro c
    obtain ⟨x,hx⟩ := h.top_surjective c
    exact ⟨(x,1),hx⟩
  center := (firstKernel h).ker
  center_comm := by
    intro z hz p
    apply Subtype.ext
    apply Prod.ext
    · have hz1 : (z : H × B).1 = 1 := by
        have he := MonoidHom.mem_ker.mp hz
        exact congrArg Subtype.val he
      change (z : H × B).1 * (p : H × B).1 =
        (p : H × B).1 * (z : H × B).1
      simp [hz1]
    · exact mul_comm _ _
  center_twoGroup := by
    apply hB.of_injective ((centralKernel h).comp (firstKernel h).ker.subtype)
    intro z z' he
    apply Subtype.ext
    apply Subtype.ext
    apply Prod.ext
    · have hz := congrArg Subtype.val (MonoidHom.mem_ker.mp z.2)
      have hz' := congrArg Subtype.val (MonoidHom.mem_ker.mp z'.2)
      exact hz.trans hz'.symm
    · exact he
  layers := h.layers
  coord := fun k => (h.coord k).comp (firstKernel h)
  coord_center := by
    intro k z hz
    change h.coord k (firstKernel h z) = 1
    rw [MonoidHom.mem_ker.mp hz, map_one]
  coord_joint := by
    intro p hp
    rw [MonoidHom.mem_ker]
    apply hjoint
    apply Prod.ext
    · simpa using hp i
    · simpa using hp j
  coord_twisted := by
    intro q p k
    change h.coord k (firstKernel h (MulAut.conjNormal q p)) = _
    rw [firstKernel_conj, h.coord_twisted]
    rfl
  coord_zero_surjective := by
    intro v
    obtain ⟨p,hp⟩ := h.coord_zero_surjective v
    refine ⟨⟨((p : H),1),p.2⟩,?_⟩
    exact hp

/-- Central rank at most two and two jointly faithful scalar coordinates
instantiate the exact joint-count target interface. -/
def jointData : ScalarFourDoubleHeadJointData (H × B) where
  headed := headed h i j hjoint hB
  first := i
  second := j
  invariant := fun k => (b k).comp (centralKernel h)
  invariant_conj := by
    intro q p k
    change b k (centralKernel h (MulAut.conjNormal q p)) = _
    rw [centralKernel_conj]
    rfl
  joint := by
    intro p p' he
    have hcoords := congrArg Prod.snd he
    have hfirst : firstKernel h p = firstKernel h p' := hjoint hcoords
    have hcentral : centralKernel h p = centralKernel h p' :=
      bjoint (congrArg Prod.fst he)
    apply Subtype.ext
    exact Prod.ext (congrArg Subtype.val hfirst) hcentral

end ScalarFourDoubleHeadCentralProduct
end SymmetricSubgroupAsymptotics
end
