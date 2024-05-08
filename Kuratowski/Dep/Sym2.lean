import Mathlib.Data.Sym.Sym2
-- import Mathlib


namespace Sym2

instance Functor : Functor Sym2 where
  map f := Sym2.map f

@[simp]
lemma Functor.eq_map {α β : Type u} (f : α → β) :
  (f <$> ·) = Sym2.map f := by
  rfl

instance LawfulFunctor : LawfulFunctor Sym2 where
  map_const := by
    intro α β
    rfl
    done
  id_map := by
    intro α sa
    change Sym2.map id sa = sa
    simp only [id_eq, map_id']
    done
  comp_map := by
    intro α β γ f g sa
    change Sym2.map (g ∘ f) sa = Sym2.map g (Sym2.map f sa)
    rw [Sym2.map_map]
    done

-- lemma FunctorSetLikeCommute {α β : Type u} (f : α → β) :
--   (SetLike.coe ∘ (f <$> ·) : Sym2 α → Set β) = (f <$> ·) ∘ SetLike.coe := by
--   ext s b
--   simp
--   done


variable {α : Type*}

lemma out_mk_eq_or_swap (v w : α) : Quot.out s(v, w) = (v, w) ∨ Quot.out s(v, w) = (w, v) := by
  unfold Quot.out
  obtain h := Classical.choose_spec (@Quot.exists_rep (α × α) (Sym2.Rel α) s(v, w))
  simp only [Sym2.eq, Sym2.rel_iff', Prod.swap_prod_mk, or_self] at h ⊢
  exact h

lemma eq_mk_out (x : Sym2 α) : x = s(x.out.1, x.out.2) := by
  simp only [Prod.mk.eta, Quot.out_eq]

lemma eq_iff_out_eq_or_out_swap (x : Sym2 α) (v w : α) :
  x = s(v, w) ↔ x.out = (v, w) ∨ x.out = (w, v) := by
  constructor
  · rintro rfl
    exact Sym2.out_mk_eq_or_swap v w
  · rintro (h | h) <;> rw [Sym2.eq_mk_out x, Sym2.eq_iff] <;> simp [h]

-- lemma CanLiftSym2Subtype (p : α → Prop) :
--   ∀ (x : Sym2 α), (∀ i ∈ x, p i) → ∃ y : Sym2 (Subtype p), Sym2.map (fun x ↦ ↑x) y = x := by
--   intro x h
--   rw [Sym2.eq_mk_out x] at h ⊢
--   simp_rw [Sym2.mem_iff] at h
--   use Sym2.mk (⟨ x.out.1, h x.out.1 (by simp) ⟩, ⟨ x.out.2, h x.out.2 (by simp) ⟩)
--   simp
--   done

instance instCanLiftSym2Subtype (p : α → Prop) :
  CanLift (Sym2 α) (Sym2 (Subtype p)) (Sym2.map (·.1)) (fun x => ∀ i ∈ x, p i) where
  prf := by
    intro x h
    rw [Sym2.eq_mk_out x] at h ⊢
    simp_rw [Sym2.mem_iff] at h
    use Sym2.mk (⟨ x.out.1, h x.out.1 (by simp) ⟩, ⟨ x.out.2, h x.out.2 (by simp) ⟩)
    simp
    done

instance instCanLiftSym2CanLift [CanLift α β f p] :
  CanLift (Sym2 α) (Sym2 β) (Sym2.map f) (fun x => ∀ i ∈ x, p i) where
  prf := by
    intro x h
    have : ∀ (x : α), p x → ∃ (y : β), f y = x := CanLift.prf
    obtain ⟨ y1, hy1 ⟩ := this x.out.1 (h x.out.1 (Sym2.out_fst_mem x))
    obtain ⟨ y2, hy2 ⟩ := this x.out.2 (h x.out.2 (Sym2.out_snd_mem x))
    use s(y1, y2)
    simp [hy1, hy2]
    done

noncomputable def liftSym2lift [CanLift α β f p] (x : Sym2 α) (h : ∀ i ∈ x, p i) : Sym2 β := by
  let a : ∃ y, map f y = x := CanLift.prf x h
  choose y _ using a
  exact y


theorem subtype_iff_mem_sat {α : Type u} {p : α → Prop} :
  ∀ x : Sym2 α, (∀ y ∈ x, p y) ↔ ∃ x' : Sym2 {x // p x}, x'.map (·.1) = x := by
  intro x
  constructor
  · -- 1.
    intro h
    lift x to Sym2 (Subtype p) using h
    use x
    done
  · -- 2.
    rintro ⟨ x', hx' ⟩ y hy
    rw [Sym2.eq_mk_out x', Sym2.map_pair_eq] at hx'
    rw [← hx'] at hy
    simp at hy
    rcases hy with rfl | rfl
    exact x'.out.1.2
    exact x'.out.2.2
    done


instance CoeSym2Coercion {α : Type u} {β : Type v} [Coe α β] :
  Coe (Sym2 α) (Sym2 β) where
  coe x := x.map (↑)


end Sym2
