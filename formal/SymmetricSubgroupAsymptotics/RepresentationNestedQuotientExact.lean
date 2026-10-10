import SymmetricSubgroupAsymptotics.RepresentationNestedQuotientImage

/-!
# Exact maps between nested representation quotients

An intertwiner sends a nested quotient `B/A` onto the quotient of its two
images.  When a second intertwiner identifies the kernel, the kernel of this
induced quotient map is the quotient of the two corresponding preimages.
This is the representation-theoretic form of the two pair-constant / pair-sum
layers used by the paired-eight omega filtration.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped Classical

namespace SymmetricSubgroupAsymptotics

universe u

variable {k G U V W : Type u} [Field k] [Group G]
  [AddCommGroup U] [Module k U]
  [AddCommGroup V] [Module k V]
  [AddCommGroup W] [Module k W]

theorem intertwinerImage_mono
    (rho : Representation k G V) (tau : Representation k G W)
    (q : rho.IntertwiningMap tau)
    {A B : Subrepresentation rho} (hAB : A ≤ B) :
    intertwinerImage rho tau q A ≤ intertwinerImage rho tau q B := by
  rintro _ ⟨a, ha, rfl⟩
  exact ⟨a, hAB ha, rfl⟩

theorem intertwinerPreimage_mono
    (rho : Representation k G U) (tau : Representation k G V)
    (i : rho.IntertwiningMap tau)
    {A B : Subrepresentation tau} (hAB : A ≤ B) :
    intertwinerPreimage rho tau i A ≤ intertwinerPreimage rho tau i B :=
  fun _ ha ↦ hAB ha

/-- The map on `B/A` induced by an intertwiner, with the target written as
the quotient of the exact images. -/
noncomputable def nestedQuotientMap
    (rho : Representation k G V) (tau : Representation k G W)
    (q : rho.IntertwiningMap tau)
    (A B : Subrepresentation rho) (hAB : A ≤ B) :
    (nestedQuotientRepresentation A B hAB).IntertwiningMap
      (nestedQuotientRepresentation
        (intertwinerImage rho tau q A)
        (intertwinerImage rho tau q B)
        (intertwinerImage_mono rho tau q hAB)) where
  toLinearMap :=
    (nestedSubrepresentation A B hAB).toSubmodule.liftQ
      ((nestedSubrepresentation
        (intertwinerImage rho tau q A)
        (intertwinerImage rho tau q B)
        (intertwinerImage_mono rho tau q hAB)).toSubmodule.mkQ.comp
          { toFun := fun b ↦ ⟨q b.1, ⟨b.1, b.2, rfl⟩⟩
            map_add' := by intro x y; exact Subtype.ext (map_add q x.1 y.1)
            map_smul' := by intro c x; exact Subtype.ext (map_smul q c x.1) })
      (by
        intro a ha
        rw [Submodule.Quotient.mk_eq_zero]
        exact ⟨a.1, ha, rfl⟩)
  isIntertwining' := by
    intro g
    apply LinearMap.ext
    intro x
    obtain ⟨b, rfl⟩ :=
      (nestedSubrepresentation A B hAB).toSubmodule.mkQ_surjective x
    apply congrArg
      (nestedSubrepresentation
        (intertwinerImage rho tau q A)
        (intertwinerImage rho tau q B)
        (intertwinerImage_mono rho tau q hAB)).toSubmodule.mkQ
    apply Subtype.ext
    exact Representation.IntertwiningMap.isIntertwining rho tau q g b.1

theorem nestedQuotientMap_surjective
    (rho : Representation k G V) (tau : Representation k G W)
    (q : rho.IntertwiningMap tau)
    (A B : Subrepresentation rho) (hAB : A ≤ B) :
    Function.Surjective (nestedQuotientMap rho tau q A B hAB) := by
  intro y
  obtain ⟨w, rfl⟩ :=
    (nestedSubrepresentation
      (intertwinerImage rho tau q A)
      (intertwinerImage rho tau q B)
      (intertwinerImage_mono rho tau q hAB)).toSubmodule.mkQ_surjective y
  obtain ⟨b, hb, hbw⟩ := w.2
  let bB : B.toSubmodule := ⟨b, hb⟩
  refine ⟨Submodule.Quotient.mk bB, ?_⟩
  apply Submodule.Quotient.eq.mpr
  apply Subtype.ext
  exact hbw

/-- The preimage of `A` inside the exact kernel source lies in the preimage
of `B`. -/
theorem nestedKernelPreimage_mono
    (sigma : Representation k G U)
    (rho : Representation k G V)
    (i : sigma.IntertwiningMap rho)
    {A B : Subrepresentation rho} (hAB : A ≤ B) :
    intertwinerPreimage sigma rho i A ≤
      intertwinerPreimage sigma rho i B :=
  intertwinerPreimage_mono sigma rho i hAB

/-- Under an exact kernel presentation `range(i)=ker(q)`, the kernel of the
induced map on `B/A` is the quotient of the two restricted kernel
preimages. -/
noncomputable def nestedQuotientMapKernelEquiv
    (sigma : Representation k G U)
    (rho : Representation k G V)
    (tau : Representation k G W)
    (i : sigma.IntertwiningMap rho)
    (q : rho.IntertwiningMap tau)
    (hi : Function.Injective i)
    (hexact : LinearMap.range i.toLinearMap = LinearMap.ker q.toLinearMap)
    (A B : Subrepresentation rho) (hAB : A ≤ B) :
    (nestedQuotientRepresentation
      (intertwinerPreimage sigma rho i A)
      (intertwinerPreimage sigma rho i B)
      (nestedKernelPreimage_mono sigma rho i hAB)).Equiv
      (nestedQuotientMap rho tau q A B hAB).ker.toRepresentation := by
  let PA := intertwinerPreimage sigma rho i A
  let PB := intertwinerPreimage sigma rho i B
  let hPAB := nestedKernelPreimage_mono sigma rho i hAB
  let Q := nestedQuotientMap rho tau q A B hAB
  let f : (nestedQuotientRepresentation PA PB hPAB).IntertwiningMap
      Q.ker.toRepresentation where
    toLinearMap :=
      (nestedSubrepresentation PA PB hPAB).toSubmodule.liftQ
        { toFun := fun c ↦
            ⟨Submodule.Quotient.mk
              (⟨i c.1.1, c.1.2⟩ : B.toSubmodule), by
                apply Submodule.Quotient.eq.mpr
                change q (i c.1.1) ∈
                  (intertwinerImage rho tau q A).toSubmodule
                have hzero : q (i c.1.1) = 0 := by
                  apply LinearMap.mem_ker.mp
                  rw [← hexact]
                  exact ⟨c.1.1, rfl⟩
                rw [hzero]
                exact Submodule.zero_mem _⟩
          map_add' := by intro x y; apply Subtype.ext; rfl
          map_smul' := by intro c x; apply Subtype.ext; rfl }
        (by
          intro c hc
          apply Subtype.ext
          rw [Submodule.Quotient.mk_eq_zero]
          exact hc)
    isIntertwining' := by
      intro g
      apply LinearMap.ext
      intro x
      obtain ⟨c, rfl⟩ :=
        (nestedSubrepresentation PA PB hPAB).toSubmodule.mkQ_surjective x
      apply Subtype.ext
      apply congrArg (nestedSubrepresentation A B hAB).toSubmodule.mkQ
      apply Subtype.ext
      exact Representation.IntertwiningMap.isIntertwining sigma rho i g c.1
  apply f.ofBijective
  constructor
  · intro x y hxy
    obtain ⟨c, rfl⟩ :=
      (nestedSubrepresentation PA PB hPAB).toSubmodule.mkQ_surjective x
    obtain ⟨d, rfl⟩ :=
      (nestedSubrepresentation PA PB hPAB).toSubmodule.mkQ_surjective y
    apply Submodule.Quotient.eq.mpr
    have hmem : i (c.1.1 - d.1.1) ∈ A.toSubmodule := by
      have hquot := congrArg Subtype.val hxy
      exact Submodule.Quotient.eq.mp hquot
    exact hmem
  · intro z
    obtain ⟨b, rfl⟩ :=
      (nestedSubrepresentation A B hAB).toSubmodule.mkQ_surjective z.1
    have hqA : q b.1 ∈ (intertwinerImage rho tau q A).toSubmodule := by
      have hz := z.2
      change Q (Submodule.Quotient.mk b) = 0 at hz
      exact Submodule.Quotient.mk_eq_zero.mp hz
    obtain ⟨a, ha, hab⟩ := hqA
    have hba : b.1 - a ∈ LinearMap.ker q.toLinearMap := by
      rw [LinearMap.mem_ker, map_sub, hab, sub_self]
    rw [← hexact] at hba
    obtain ⟨c, hc⟩ := hba
    have hcPB : c ∈ PB := by
      change i c ∈ B
      rw [hc]
      exact B.toSubmodule.sub_mem b.2 (hAB ha)
    let cPB : PB.toSubmodule := ⟨c, hcPB⟩
    refine ⟨Submodule.Quotient.mk cPB, ?_⟩
    apply Subtype.ext
    apply Submodule.Quotient.eq.mpr
    change i c - b.1 ∈ A
    rw [hc]
    simpa only [sub_sub_cancel_left] using A.toSubmodule.neg_mem ha

end SymmetricSubgroupAsymptotics

end
