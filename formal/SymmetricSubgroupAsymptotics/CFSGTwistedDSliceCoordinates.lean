import SymmetricSubgroupAsymptotics.CFSGTwistedDHyperbolicCoordinates

/-! Literal reassociation of the original fixed coordinates into a
hyperbolic part and the anisotropic norm coordinate. The hyperbolic form
and every slice vector are actual linear restrictions of the SAME Q. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGTwistedDSliceCoordinates
open CFSGTwistedDLinearParameters CFSGTwistedDFixedQuadraticSpace
open CFSGTwistedDHyperbolicCoordinates CFSGTwistedDAnisotropicNormForm CFSGTwistedA2FixedField

def splitEquiv (n : ℕ) (q : CFSG.PrimePower) :
    fixedSpace n q ≃ₗ[fixedField q]
      (((Fin (n + 1) → fixedField q) × (Fin (n + 1) → fixedField q)) × q.Extension 2) :=
  (linearParameters n q).trans
    { toFun := fun x => ((x.1, x.2.1), x.2.2)
      invFun := fun x => (x.1.1, (x.1.2, x.2))
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }

def hyperbolicPart (n : ℕ) (q : CFSG.PrimePower) :
    fixedSpace n q →ₗ[fixedField q]
      ((Fin (n + 1) → fixedField q) × (Fin (n + 1) → fixedField q)) :=
  (LinearMap.fst (fixedField q)
    ((Fin (n + 1) → fixedField q) × (Fin (n + 1) → fixedField q)) (q.Extension 2)).comp
      (splitEquiv n q).toLinearMap

def hyperbolicEmbedding (n : ℕ) (q : CFSG.PrimePower) :
    ((Fin (n + 1) → fixedField q) × (Fin (n + 1) → fixedField q)) →ₗ[fixedField q] fixedSpace n q :=
  (splitEquiv n q).symm.toLinearMap.comp
    (LinearMap.inl (fixedField q)
      ((Fin (n + 1) → fixedField q) × (Fin (n + 1) → fixedField q)) (q.Extension 2))

def hyperbolicForm (n : ℕ) (q : CFSG.PrimePower) :
    QuadraticForm (fixedField q)
      ((Fin (n + 1) → fixedField q) × (Fin (n + 1) → fixedField q)) :=
  (fixedQuadraticForm n q).comp (hyperbolicEmbedding n q)

def sliceVector (n : ℕ) (q : CFSG.PrimePower)
    (h : (Fin (n + 1) → fixedField q) × (Fin (n + 1) → fixedField q)) (a : q.Extension 2) :
    fixedSpace n q := (splitEquiv n q).symm (h, a)

theorem split_sliceVector (n : ℕ) (q : CFSG.PrimePower)
    (h : (Fin (n + 1) → fixedField q) × (Fin (n + 1) → fixedField q)) (a : q.Extension 2) :
    splitEquiv n q (sliceVector n q h a) = (h, a) :=
  (splitEquiv n q).apply_symm_apply _

theorem sliceVector_parameters (n : ℕ) (q : CFSG.PrimePower)
    (h : (Fin (n + 1) → fixedField q) × (Fin (n + 1) → fixedField q)) (a : q.Extension 2) :
    linearParameters n q (sliceVector n q h a) = (h.1, (h.2, a)) :=
  (linearParameters n q).apply_symm_apply _

theorem sliceVector_positive (n : ℕ) (q : CFSG.PrimePower)
    (h : (Fin (n + 1) → fixedField q) × (Fin (n + 1) → fixedField q)) (a : q.Extension 2) :
    positivePart n q (sliceVector n q h a) = h.1 :=
  congrArg Prod.fst (sliceVector_parameters n q h a)

theorem sliceVector_negative (n : ℕ) (q : CFSG.PrimePower)
    (h : (Fin (n + 1) → fixedField q) × (Fin (n + 1) → fixedField q)) (a : q.Extension 2) :
    negativePart n q (sliceVector n q h a) = h.2 :=
  congrArg (fun x => x.2.1) (sliceVector_parameters n q h a)

theorem sliceVector_anisotropic (n : ℕ) (q : CFSG.PrimePower)
    (h : (Fin (n + 1) → fixedField q) × (Fin (n + 1) → fixedField q)) (a : q.Extension 2) :
    anisotropicPart n q (sliceVector n q h a) = a :=
  congrArg (fun x => x.2.2) (sliceVector_parameters n q h a)

theorem sliceVector_hyperbolic (n : ℕ) (q : CFSG.PrimePower)
    (h : (Fin (n + 1) → fixedField q) × (Fin (n + 1) → fixedField q)) (a : q.Extension 2) :
    hyperbolicPart n q (sliceVector n q h a) = h :=
  congrArg Prod.fst (split_sliceVector n q h a)

theorem quadratic_sliceVector (n : ℕ) (q : CFSG.PrimePower)
    (h : (Fin (n + 1) → fixedField q) × (Fin (n + 1) → fixedField q)) (a : q.Extension 2) :
    fixedQuadraticForm n q (sliceVector n q h a) = dotProduct h.1 h.2 + normForm q a := by
  rw [quadratic_parts, sliceVector_positive, sliceVector_negative, sliceVector_anisotropic]

theorem hyperbolicForm_apply (n : ℕ) (q : CFSG.PrimePower)
    (h : (Fin (n + 1) → fixedField q) × (Fin (n + 1) → fixedField q)) :
    hyperbolicForm n q h = dotProduct h.1 h.2 := by
  change fixedQuadraticForm n q (sliceVector n q h 0) = _
  rw [quadratic_sliceVector, QuadraticMap.map_zero, add_zero]

theorem sliceVector_nonzero (n : ℕ) (q : CFSG.PrimePower)
    (h : (Fin (n + 1) → fixedField q) × (Fin (n + 1) → fixedField q)) (a : q.Extension 2)
    (hh : h ≠ 0) : sliceVector n q h a ≠ 0 := by
  intro he
  have hv := congrArg (hyperbolicPart n q) he
  rw [sliceVector_hyperbolic, map_zero] at hv
  exact hh hv

theorem span_sliceVector_unique (n : ℕ) (q : CFSG.PrimePower)
    (h : (Fin (n + 1) → fixedField q) × (Fin (n + 1) → fixedField q)) (hh : h ≠ 0)
    (a b : q.Extension 2)
    (he : Submodule.span (fixedField q) {sliceVector n q h a} =
      Submodule.span (fixedField q) {sliceVector n q h b}) : a = b := by
  have hm : sliceVector n q h a ∈ Submodule.span (fixedField q) {sliceVector n q h b} :=
    he ▸ Submodule.mem_span_singleton_self _
  obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp hm
  have hp := congrArg (hyperbolicPart n q) hc
  rw [map_smul, sliceVector_hyperbolic, sliceVector_hyperbolic] at hp
  have hc1 : c = 1 := smul_left_injective (fixedField q) hh
    (hp.trans (one_smul (fixedField q) h).symm)
  have hv := congrArg (anisotropicPart n q) hc
  rw [map_smul, sliceVector_anisotropic, sliceVector_anisotropic, hc1, one_smul] at hv
  exact hv.symm

end SymmetricSubgroupAsymptotics.CFSGTwistedDSliceCoordinates
