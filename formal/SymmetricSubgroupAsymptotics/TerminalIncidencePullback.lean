import SymmetricSubgroupAsymptotics.TerminalIncidenceRecords

/-! Literal pullback extensions and scalar characters of their original kernel. -/

set_option autoImplicit false
noncomputable section

namespace SymmetricSubgroupAsymptotics

variable {X Y G K : Type} [Group X] [Group Y] [Group G]
    [AddCommGroup K] [Module (ZMod 2) K]

/-- The actual fibre product subgroup, not a new group specified by its order. -/
def terminalPullbackGroup (π : X →* Y) (f : G →* Y) : Subgroup (X × G) :=
  (π.comp (MonoidHom.fst X G)).eqLocus (f.comp (MonoidHom.snd X G))

/-- Projection from the literal pullback to the complete source. -/
def terminalPullbackProjection (π : X →* Y) (f : G →* Y) :
    terminalPullbackGroup π f →* G :=
  (MonoidHom.snd X G).comp (terminalPullbackGroup π f).subtype

private def terminalPullbackKernelHom (π : X →* Y)
    (e : Multiplicative K ≃* π.ker) (f : G →* Y) :
    Multiplicative K →* (terminalPullbackProjection π f).ker where
  toFun z := ⟨⟨(terminalKernelInclusion π e z,1),by
    change π (terminalKernelInclusion π e z)=f 1
    simp⟩,rfl⟩
  map_one' := by apply Subtype.ext; apply Subtype.ext; simp
  map_mul' z w := by apply Subtype.ext; apply Subtype.ext; simp

omit [Module (ZMod 2) K] in
private theorem terminalPullbackKernelHom_bijective (π : X →* Y)
    (e : Multiplicative K ≃* π.ker) (f : G →* Y) :
    Function.Bijective (terminalPullbackKernelHom π e f) := by
  constructor
  · intro z w h
    apply terminalKernelInclusion_injective π e
    exact congrArg (fun z => z.1.1.1) h
  · intro g
    have hg : g.1.1.2=1 := g.2
    have hπg : π g.1.1.1=1 := by
      have h := g.1.2
      change π g.1.1.1=f g.1.1.2 at h
      simpa only [hg,map_one] using h
    refine ⟨e.symm ⟨g.1.1.1,hπg⟩,?_⟩
    apply Subtype.ext
    apply Subtype.ext
    apply Prod.ext
    · exact congrArg Subtype.val (e.apply_symm_apply _)
    · exact hg.symm

/-- The same original kernel chart, transported without changing coordinates. -/
def terminalPullbackKernelChart (π : X →* Y)
    (e : Multiplicative K ≃* π.ker) (f : G →* Y) :
    Multiplicative K ≃* (terminalPullbackProjection π f).ker :=
  MulEquiv.ofBijective (terminalPullbackKernelHom π e f)
    (terminalPullbackKernelHom_bijective π e f)

omit [Module (ZMod 2) K] in
@[simp] theorem terminalPullbackKernelInclusion_val (π : X →* Y)
    (e : Multiplicative K ≃* π.ker) (f : G →* Y) (z : Multiplicative K) :
    (terminalKernelInclusion (terminalPullbackProjection π f)
      (terminalPullbackKernelChart π e f) z).1 = (terminalKernelInclusion π e z,1) := rfl

/-- A literal section lifted to the actual pullback. -/
def terminalPullbackSection (π : X →* Y) (f : G →* Y)
    (s : Y → X) (hs : ∀ y, π (s y)=y) (g : G) : terminalPullbackGroup π f :=
  ⟨(s (f g),g),hs (f g)⟩

theorem terminalPullbackProjection_surjective (π : X →* Y) (f : G →* Y)
    (s : Y → X) (hs : ∀ y, π (s y)=y) :
    Function.Surjective (terminalPullbackProjection π f) :=
  fun g => ⟨terminalPullbackSection π f s hs g,rfl⟩

/-- An actual extending character makes the scalar chosen-section cocycle
a coboundary on the complete source. This connects the original splitting
annihilator to concrete coordinate cocycles without changing sections by fiat. -/
theorem terminalPullback_annihilator_coboundary
    (π : X →* Y) (e : Multiplicative K ≃* π.ker) (f : G →* Y)
    (s : Y → X) (hs : ∀ y, π (s y)=y)
    (c : Y → Y → K)
    (hc : ∀ y z, s y*s z = terminalKernelInclusion π e (Multiplicative.ofAdd (c y z))*s (y*z))
    (ell : Module.Dual (ZMod 2) K)
    (hell : ell ∈ terminalSplittingAnnihilator (terminalPullbackProjection π f)
      (terminalPullbackKernelChart π e f)) :
    (fun xy : G × G => ell (c (f xy.1) (f xy.2))) ∈
      groupCohomology.coboundaries₂ (Rep.trivial (ZMod 2) G (ZMod 2)) := by
  obtain ⟨χ,hχ⟩ := (mem_terminalSplittingAnnihilator _ _ ell).mp hell
  let t := terminalPullbackSection π f s hs
  have ht (x y : G) : t x*t y =
      terminalKernelInclusion (terminalPullbackProjection π f)
        (terminalPullbackKernelChart π e f) (Multiplicative.ofAdd (c (f x) (f y))) * t (x*y) := by
    apply Subtype.ext
    apply Prod.ext
    · change s (f x)*s (f y) =
        terminalKernelInclusion π e (Multiplicative.ofAdd (c (f x) (f y)))*s (f (x*y))
      rw [map_mul,hc]
    · simp [t,terminalPullbackSection]
  refine ⟨fun x => χ (Additive.ofMul (t x)),funext fun xy => ?_⟩
  have hx := χ.map_add (Additive.ofMul (t xy.1)) (Additive.ofMul (t xy.2))
  change χ (Additive.ofMul (t xy.1*t xy.2)) =
    χ (Additive.ofMul (t xy.1))+χ (Additive.ofMul (t xy.2)) at hx
  rw [ht] at hx
  have hz := χ.map_add
    (Additive.ofMul (terminalKernelInclusion (terminalPullbackProjection π f)
      (terminalPullbackKernelChart π e f) (Multiplicative.ofAdd (c (f xy.1) (f xy.2)))))
    (Additive.ofMul (t (xy.1*xy.2)))
  rw [hχ] at hz
  change χ (Additive.ofMul (t xy.2)) - χ (Additive.ofMul (t (xy.1*xy.2))) +
    χ (Additive.ofMul (t xy.1)) = ell (c (f xy.1) (f xy.2))
  change χ (Additive.ofMul
    (terminalKernelInclusion (terminalPullbackProjection π f)
      (terminalPullbackKernelChart π e f) (Multiplicative.ofAdd (c (f xy.1) (f xy.2))) *
      t (xy.1*xy.2))) = ell (c (f xy.1) (f xy.2)) + χ (Additive.ofMul (t (xy.1*xy.2))) at hz
  have he := hx.symm.trans hz
  linear_combination he

end SymmetricSubgroupAsymptotics
