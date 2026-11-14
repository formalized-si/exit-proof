/-
  Small list facts used by the model: sums of a weight over a list, and how `eraseIdx`, `set`
  and `map` interact.
-/
namespace Intents

theorem ifP {c : Prop} [Decidable c] {α : Sort _} {a b : α} (h : c) : (if c then a else b) = a := by
  simp [h]

theorem ifN {c : Prop} [Decidable c] {α : Sort _} {a b : α} (h : ¬c) : (if c then a else b) = b := by
  simp [h]

/-- Sum of a weight over a list. -/
def sumBy {α : Type} (f : α → Nat) : List α → Nat
  | [] => 0
  | a :: t => f a + sumBy f t

theorem sumBy_nil {α : Type} (f : α → Nat) : sumBy f [] = 0 := rfl

theorem sumBy_cons {α : Type} (f : α → Nat) (a : α) (t : List α) :
    sumBy f (a :: t) = f a + sumBy f t := rfl

theorem sumBy_one {α : Type} (f : α → Nat) (a : α) : sumBy f [a] = f a := by
  simp [sumBy]

theorem sumBy_append {α : Type} (f : α → Nat) (l₁ l₂ : List α) :
    sumBy f (l₁ ++ l₂) = sumBy f l₁ + sumBy f l₂ := by
  induction l₁ with
  | nil => simp [sumBy]
  | cons a t ih => simp only [List.cons_append, sumBy, ih]; omega

theorem sumBy_eraseIdx {α : Type} (f : α → Nat) {l : List α} {i : Nat} {a : α}
    (h : l[i]? = some a) : sumBy f (l.eraseIdx i) + f a = sumBy f l := by
  induction l generalizing i with
  | nil => simp at h
  | cons b t ih =>
    cases i with
    | zero =>
      simp only [List.getElem?_cons_zero, Option.some.injEq] at h
      subst h
      simp only [List.eraseIdx_cons_zero, sumBy]; omega
    | succ n =>
      simp only [List.getElem?_cons_succ] at h
      have := ih h
      simp only [List.eraseIdx_cons_succ, sumBy]; omega

theorem sumBy_set {α : Type} (f : α → Nat) {l : List α} {i : Nat} {a : α}
    (h : l[i]? = some a) (b : α) : sumBy f (l.set i b) + f a = sumBy f l + f b := by
  induction l generalizing i with
  | nil => simp at h
  | cons c t ih =>
    cases i with
    | zero =>
      simp only [List.getElem?_cons_zero, Option.some.injEq] at h
      subst h
      simp only [List.set_cons_zero, sumBy]; omega
    | succ n =>
      simp only [List.getElem?_cons_succ] at h
      have := ih h
      simp only [List.set_cons_succ, sumBy]; omega

theorem sumBy_eq_zero {α : Type} (f : α → Nat) {l : List α} (h : ∀ a ∈ l, f a = 0) :
    sumBy f l = 0 := by
  induction l with
  | nil => rfl
  | cons a t ih =>
    have h1 := h a (by simp)
    have h2 := ih (fun b hb => h b (by simp [hb]))
    simp only [sumBy]; omega

theorem le_sumBy {α : Type} (f : α → Nat) {l : List α} {a : α} (h : a ∈ l) :
    f a ≤ sumBy f l := by
  induction l with
  | nil => simp at h
  | cons b t ih =>
    rcases List.mem_cons.mp h with rfl | h'
    · simp only [sumBy]; omega
    · have := ih h'; simp only [sumBy]; omega

theorem map_eraseIdx {α β : Type} (f : α → β) (l : List α) (i : Nat) :
    (l.eraseIdx i).map f = (l.map f).eraseIdx i := by
  induction l generalizing i with
  | nil => simp
  | cons a t ih =>
    cases i with
    | zero => simp
    | succ n => simp [ih]

/-- Replacing an element by one with the same image leaves the image of the list unchanged. -/
theorem map_set_same {α β : Type} (f : α → β) {l : List α} {i : Nat} {a : α}
    (h : l[i]? = some a) (b : α) (hb : f b = f a) : (l.set i b).map f = l.map f := by
  induction l generalizing i with
  | nil => simp at h
  | cons c t ih =>
    cases i with
    | zero =>
      simp only [List.getElem?_cons_zero, Option.some.injEq] at h
      subst h
      simp [hb]
    | succ n =>
      simp only [List.getElem?_cons_succ] at h
      simp [ih h]

end Intents
