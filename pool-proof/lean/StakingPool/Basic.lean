/-
  Basic lemmas: the error monad, checked arithmetic, rounding arithmetic,
  and sums over the accounts map.
-/
import StakingPool.Model

namespace StakingPool

/-! ## Except monad -/

theorem bind_ok {α β} {x : M α} {f : α → M β} {r : β} :
    (x >>= f) = .ok r ↔ ∃ a, x = .ok a ∧ f a = .ok r := by
  cases x <;> simp [bind, Except.bind]

theorem pure_ok {α} {a r : α} : (pure a : M α) = .ok r ↔ a = r := by
  simp [pure, Except.pure]

theorem throw_ok {α} {m : String} {r : α} : (throw m : M α) = .ok r ↔ False := by
  simp [throw, throwThe, MonadExceptOf.throw]

theorem ensure_ok {p : Prop} [Decidable p] {m : String} {u : Unit} : ensure p m = .ok u ↔ p := by
  unfold ensure; split <;> simp_all [pure, Except.pure, throw, throwThe, MonadExceptOf.throw]

theorem add128_ok {a b r : Nat} : add128 a b = .ok r ↔ a + b ≤ U128_MAX ∧ r = a + b := by
  unfold add128; split <;> simp_all [pure, Except.pure, throw, throwThe, MonadExceptOf.throw] <;> omega

theorem add64_ok {a b r : Nat} : add64 a b = .ok r ↔ a + b ≤ U64_MAX ∧ r = a + b := by
  unfold add64; split <;> simp_all [pure, Except.pure, throw, throwThe, MonadExceptOf.throw] <;> omega

theorem sub128_ok {a b r : Nat} : sub128 a b = .ok r ↔ b ≤ a ∧ r = a - b := by
  unfold sub128; split <;> simp_all [pure, Except.pure, throw, throwThe, MonadExceptOf.throw] <;> omega

theorem asU128_ok {x r : Nat} : asU128 x = .ok r ↔ x ≤ U128_MAX ∧ r = x := by
  unfold asU128; split <;> simp_all [pure, Except.pure, throw, throwThe, MonadExceptOf.throw] <;> omega

theorem ite_ok {α} {p : Prop} [Decidable p] {a b : M α} {r : α} :
    (if p then a else b) = .ok r ↔ (p ∧ a = .ok r) ∨ (¬p ∧ b = .ok r) := by
  split <;> simp_all

/-- Ok results of the rounding helpers. -/
theorem sharesDown_ok {c : Contract} {x r : Nat} :
    c.sharesDown x = .ok r ↔ c.s ≠ 0 ∧ c.ts * x / c.s ≤ U128_MAX ∧ r = c.ts * x / c.s := by
  simp [Contract.sharesDown, bind_ok, ensure_ok, asU128_ok]

theorem sharesUp_ok {c : Contract} {x r : Nat} :
    c.sharesUp x = .ok r ↔ c.s ≠ 0 ∧ (c.ts * x + (c.s - 1)) / c.s ≤ U128_MAX ∧
      r = (c.ts * x + (c.s - 1)) / c.s := by
  simp [Contract.sharesUp, bind_ok, ensure_ok, asU128_ok]

theorem amountDown_ok {c : Contract} {x r : Nat} :
    c.amountDown x = .ok r ↔ c.ts ≠ 0 ∧ c.s * x / c.ts ≤ U128_MAX ∧ r = c.s * x / c.ts := by
  simp [Contract.amountDown, bind_ok, ensure_ok, asU128_ok]

theorem amountUp_ok {c : Contract} {x r : Nat} :
    c.amountUp x = .ok r ↔ c.ts ≠ 0 ∧ (c.s * x + (c.ts - 1)) / c.ts ≤ U128_MAX ∧
      r = (c.s * x + (c.ts - 1)) / c.ts := by
  simp [Contract.amountUp, bind_ok, ensure_ok, asU128_ok]

/-! ## Rounding arithmetic -/

/-- floor: `(a / b) * b ≤ a` -/
theorem div_mul_le (a b : Nat) : a / b * b ≤ a := Nat.div_mul_le_self a b

/-- ceil division `(a + (b - 1)) / b` -/
def cdiv (a b : Nat) : Nat := (a + (b - 1)) / b

theorem cdiv_mul_ge {a b : Nat} (hb : 0 < b) : a ≤ (a + (b - 1)) / b * b := by
  have h1 := Nat.div_add_mod (a + (b - 1)) b
  have h2 := Nat.mod_lt (a + (b - 1)) hb
  rw [Nat.mul_comm] at h1
  omega

theorem cdiv_le_div_add_one {a b : Nat} (hb : 0 < b) : (a + (b - 1)) / b ≤ a / b + 1 := by
  have h := (Nat.div_lt_iff_lt_mul hb).2 (show a + (b - 1) < (a / b + 2) * b by
    have h1 := Nat.div_add_mod a b
    have h2 := Nat.mod_lt a hb
    rw [Nat.add_mul, Nat.mul_comm]
    omega)
  omega

theorem div_le_cdiv (a b : Nat) : a / b ≤ (a + (b - 1)) / b :=
  Nat.div_le_div_right (Nat.le_add_right _ _)

/-- `(b * q + (b - 1)) / b = q` -/
theorem cdiv_mul_self {b q : Nat} (hb : 0 < b) : (b * q + (b - 1)) / b = q := by
  rw [Nat.add_comm, Nat.add_mul_div_left _ _ hb, Nat.div_eq_of_lt (by omega)]
  simp

/-- `x ≤ y / k ↔ x * k ≤ y` -/
theorem le_div_iff {x y k : Nat} (hk : 0 < k) : x ≤ y / k ↔ x * k ≤ y := Nat.le_div_iff_mul_le hk

theorem mul_le_mul' {a b c d : Nat} (h1 : a ≤ b) (h2 : c ≤ d) : a * c ≤ b * d :=
  Nat.mul_le_mul h1 h2

/-! ## Sums over a list -/

theorem sum_map_congr {α} (l : List α) (f g : α → Nat) (h : ∀ x ∈ l, f x = g x) :
    (l.map f).sum = (l.map g).sum := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    simp only [List.map_cons, List.sum_cons]
    rw [h a (by simp), ih (fun x hx => h x (by simp [hx]))]

theorem sum_map_add {α} (l : List α) (f g : α → Nat) :
    (l.map (fun x => f x + g x)).sum = (l.map f).sum + (l.map g).sum := by
  induction l with
  | nil => rfl
  | cons a l ih => simp only [List.map_cons, List.sum_cons, ih]; omega

theorem sum_map_le {α} (l : List α) (f g : α → Nat) (h : ∀ x, f x ≤ g x) :
    (l.map f).sum ≤ (l.map g).sum := by
  induction l with
  | nil => exact Nat.le_refl _
  | cons a l ih => simp only [List.map_cons, List.sum_cons]; have := h a; omega

theorem le_sum_map {α} (l : List α) (f : α → Nat) (a : α) (ha : a ∈ l) :
    f a ≤ (l.map f).sum := by
  induction l with
  | nil => simp at ha
  | cons b l ih =>
    simp only [List.map_cons, List.sum_cons]
    rcases List.mem_cons.1 ha with h | h
    · subst h; omega
    · have := ih h; omega

/-- Updating one point of a function changes a sum over a duplicate-free list by the
difference at that point. -/
theorem sum_map_update {α} [DecidableEq α] (l : List α) (hl : l.Nodup) (f g : α → Nat) (a : α)
    (hfg : ∀ x, x ≠ a → g x = f x) (ha : a ∈ l) :
    (l.map g).sum + f a = (l.map f).sum + g a := by
  induction l with
  | nil => simp at ha
  | cons b l ih =>
    simp only [List.map_cons, List.sum_cons]
    rw [List.nodup_cons] at hl
    by_cases hb : b = a
    · subst hb
      have : (l.map g).sum = (l.map f).sum :=
        sum_map_congr l g f (fun x hx => hfg x (fun h => hl.1 (h ▸ hx)))
      omega
    · have ha' : a ∈ l := by
        rcases List.mem_cons.1 ha with h | h
        · exact absurd h.symm hb
        · exact h
      have := ih hl.2 ha'
      rw [hfg b hb]
      omega

/-! ## The accounts map -/

/-- Well-formedness of the accounts map: no duplicate ids, and every id outside the
support reads as the default account. -/
def Accts.WF (a : Accts) : Prop := a.keys.Nodup ∧ ∀ k, k ∉ a.keys → a.f k = Account.zero

theorem Accts.WF.empty : Accts.empty.WF := ⟨List.nodup_nil, fun _ _ => rfl⟩

theorem Accts.get_save (a : Accts) (id k : AccountId) (acc : Account) :
    (a.save id acc).get k = if k = id then acc.norm else a.get k := rfl

theorem Accts.get_save_self (a : Accts) (id : AccountId) (acc : Account) :
    (a.save id acc).get id = acc.norm := by simp [Accts.get_save]

theorem Accts.get_save_ne (a : Accts) {id k : AccountId} (acc : Account) (h : k ≠ id) :
    (a.save id acc).get k = a.get k := by simp [Accts.get_save, h]

theorem Accts.WF.save {a : Accts} (h : a.WF) (id : AccountId) (acc : Account) :
    (a.save id acc).WF := by
  constructor
  · simp only [Accts.save]
    split
    · exact h.1
    · exact List.nodup_cons.2 ⟨by assumption, h.1⟩
  · intro k hk
    simp only [Accts.save] at hk ⊢
    have hne : k ≠ id := by
      intro he; subst he; split at hk <;> simp_all
    simp only [hne, ite_false]
    apply h.2
    intro hm; apply hk; split <;> simp_all

/-- A "measure" on accounts: vanishes on the default account and on removed entries. -/
def Measure (g : Account → Nat) : Prop := ∀ acc : Account, g acc.norm = g acc ∧ g Account.zero = 0

theorem Accts.sum_save {a : Accts} (h : a.WF) (id : AccountId) (acc : Account)
    {g : Account → Nat} (hg : Measure g) :
    (a.save id acc).sum g + g (a.get id) = a.sum g + g acc := by
  have hz : g Account.zero = 0 := (hg acc).2
  have hn : g acc.norm = g acc := (hg acc).1
  unfold Accts.sum
  by_cases hm : id ∈ a.keys
  · have hk : (a.save id acc).keys = a.keys := by simp [Accts.save, hm]
    rw [hk]
    have := sum_map_update a.keys h.1 (fun k => g (a.f k)) (fun k => g ((a.save id acc).f k)) id
      (fun x hx => by simp [Accts.save, hx]) hm
    simp only [Accts.get] at this ⊢
    have hs : g ((a.save id acc).f id) = g acc := by simp [Accts.save, hn]
    omega
  · have hk : (a.save id acc).keys = id :: a.keys := by simp [Accts.save, hm]
    rw [hk]
    simp only [List.map_cons, List.sum_cons, Accts.get]
    have h0 : a.f id = Account.zero := h.2 id hm
    have : (a.keys.map (fun k => g ((a.save id acc).f k))).sum = (a.keys.map (fun k => g (a.f k))).sum :=
      sum_map_congr _ _ _ (fun x hx => by
        have : x ≠ id := fun he => hm (he ▸ hx)
        simp [Accts.save, this])
    rw [this, h0, hz]
    have hs : g ((a.save id acc).f id) = g acc := by simp [Accts.save, hn]
    omega

theorem Accts.le_sum {a : Accts} (h : a.WF) (id : AccountId) {g : Account → Nat}
    (hz : g Account.zero = 0) : g (a.get id) ≤ a.sum g := by
  unfold Accts.sum Accts.get
  by_cases hm : id ∈ a.keys
  · exact le_sum_map a.keys (fun k => g (a.f k)) id hm
  · rw [h.2 id hm, hz]; exact Nat.zero_le _

theorem Accts.sum_add (a : Accts) (g h : Account → Nat) :
    a.sum (fun x => g x + h x) = a.sum g + a.sum h := by
  unfold Accts.sum; exact sum_map_add _ _ _

theorem Accts.sum_le (a : Accts) {g h : Account → Nat} (hle : ∀ x, g x ≤ h x) :
    a.sum g ≤ a.sum h := by
  unfold Accts.sum; exact sum_map_le _ _ _ (fun x => hle _)

/-! ## The measures used by the invariants -/

def gU (a : Account) : Nat := a.unstaked
def gSh (a : Account) : Nat := a.stakeShares
/-- unstaked balance of accounts still cooling down after threshold epoch `t` -/
def gCool (t : Nat) (a : Account) : Nat := if t < a.availEpoch then a.unstaked else 0
/-- unstaked balance of accounts already available at threshold `t` -/
def gAvail (t : Nat) (a : Account) : Nat := if t < a.availEpoch then 0 else a.unstaked

theorem norm_cases (a : Account) : a.norm = a ∨ (a.norm = Account.zero ∧ a.unstaked = 0 ∧ a.stakeShares = 0) := by
  unfold Account.norm; split
  · right; simp_all
  · left; rfl

theorem measure_gU : Measure gU := by
  intro a; refine ⟨?_, rfl⟩
  rcases norm_cases a with h | ⟨h, h1, _⟩
  · simp [h]
  · simp [gU, h, h1, Account.zero]

theorem measure_gSh : Measure gSh := by
  intro a; refine ⟨?_, rfl⟩
  rcases norm_cases a with h | ⟨h, _, h2⟩
  · simp [h]
  · simp [gSh, h, h2, Account.zero]

theorem measure_gCool (t : Nat) : Measure (gCool t) := by
  intro a; refine ⟨?_, by simp [gCool, Account.zero]⟩
  rcases norm_cases a with h | ⟨h, h1, _⟩
  · simp [h]
  · simp [gCool, h, h1, Account.zero]

theorem measure_gAvail (t : Nat) : Measure (gAvail t) := by
  intro a; refine ⟨?_, by simp [gAvail, Account.zero]⟩
  rcases norm_cases a with h | ⟨h, h1, _⟩
  · simp [h]
  · simp [gAvail, h, h1, Account.zero]

def Contract.sumU (c : Contract) : Nat := c.accts.sum gU
def Contract.sumSh (c : Contract) : Nat := c.accts.sum gSh
def Contract.cool (c : Contract) (t : Nat) : Nat := c.accts.sum (gCool t)

theorem Contract.get_save (c : Contract) (id k : AccountId) (acc : Account) :
    (c.save id acc).get k = if k = id then acc.norm else c.get k := rfl

theorem norm_unstaked (a : Account) : a.norm.unstaked = a.unstaked := by
  rcases norm_cases a with h | ⟨h, h1, _⟩
  · simp [h]
  · simp [h, h1, Account.zero]

theorem norm_shares (a : Account) : a.norm.stakeShares = a.stakeShares := by
  rcases norm_cases a with h | ⟨h, _, h2⟩
  · simp [h]
  · simp [h, h2, Account.zero]

end StakingPool
