import Mathlib.Data.List.Basic


namespace List
variable {α : Type _}

lemma get_zero'  (l : List α) (h : l ≠ []) :
  l.get ⟨ 0, List.length_pos_iff_ne_nil.mpr h ⟩ = l.head h := by
  cases l with
  | nil => contradiction
  | cons x xs => rfl

-- lemma head_of_eq (l l' : List α) (hEq : l = l') (h : l ≠ []) :
--   l.head h = l'.head (by rwa [← hEq]) := by
--   simp only [hEq]
--   done

lemma head_reverse (l : List α) (hl : l ≠ []) :
  l.reverse.head ((not_congr List.reverse_eq_nil_iff).mpr hl) = l.getLast hl := by
  have : l.getLast hl = l.reverse.reverse.getLast (by rw [reverse_reverse]; exact hl) := by
    simp only [reverse_reverse]
    done
  rw [this, List.getLast_reverse]; clear this
  exact (get_zero' l.reverse _).symm
  done

lemma head_append {l₁ l₂ : List α} (hl : l₁ ≠ []) :
  (l₁ ++ l₂).head (by simp only [ne_eq, append_eq_nil, hl, false_and, not_false_eq_true]) =
    l₁.head hl := by
  cases l₁ with
  | nil => contradiction
  | cons x xs => rfl
  done

lemma head_singleton (x : α) (h : [x] ≠ []) :
  [x].head h = x := by
  rfl

@[simp]
lemma cons_head_tail (l : List α) (h : l ≠ []) :
  (l.head h) :: l.tail = l := by
  cases l with
  | nil => contradiction
  | cons x xs => rfl
  done

lemma tail_eq_nil {l : List α} (h : l.tail = []) :
  l = [] ∨ ∃ x, l = [x] := by
  match l with
  | [] => simp only [exists_false, or_false]
  | x :: xs =>
    rw [tail_cons] at h
    rw [h]
    simp only [cons.injEq, and_true, exists_eq', or_true]

lemma tail_eq_nil_length {l : List α} (h : l.tail = []) :
  l.length ≤ 1 := by
  rcases tail_eq_nil h with rfl | ⟨x, rfl⟩
  ·
    rw [length_nil]
    exact zero_le _
  ·
    rw [length_singleton]

lemma tail_eq_drop_one (l : List α) :
  l.tail = l.drop 1 := (drop_one l).symm

lemma getLast_tail {l : List α} (h : l.tail ≠ []) :
  l.tail.getLast h = l.getLast (List.ne_nil_of_drop_ne_nil (tail_eq_drop_one l ▸ h)) := by
  match l with
  | [] => contradiction
  | x :: xs =>
    rw [tail_cons] at h
    simp only [tail_cons, List.getLast_cons h]
    done
