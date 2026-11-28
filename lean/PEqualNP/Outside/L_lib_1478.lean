import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_lib_1478

open PEqualNP.CircuitLowerBounds

def run {α : Type} (F : Gate → List α → α) (init : List α) (gs : List Gate) : List α :=
  gs.foldl (fun ts g => ts ++ [F g ts]) init

theorem run_append {α : Type} (F : Gate → List α → α) (init : List α) (gs hs : List Gate) :
    run F init (gs ++ hs) = run F (run F init gs) hs := by
  simp [run, List.foldl_append]

theorem run_single {α : Type} (F : Gate → List α → α) (init : List α) (g : Gate) :
    run F init [g] = init ++ [F g init] := rfl

theorem run_length {α : Type} (F : Gate → List α → α) (gs : List Gate) :
    ∀ init : List α, (run F init gs).length = init.length + gs.length := by
  induction gs with
  | nil => intro init; rfl
  | cons g gs ih =>
    intro init
    show (run F (init ++ [F g init]) gs).length = _
    rw [ih]; simp; omega

theorem run_prefix {α : Type} (F : Gate → List α → α) (gs : List Gate) :
    ∀ init : List α, init <+: run F init gs := by
  induction gs with
  | nil => intro init; exact List.prefix_refl _
  | cons g gs ih =>
    intro init
    exact (List.prefix_append init [F g init]).trans (ih (init ++ [F g init]))

theorem getD_of_prefix {α : Type} {l₁ l₂ : List α} (h : l₁ <+: l₂) {i : ℕ} (hi : i < l₁.length)
    (d : α) : l₂.getD i d = l₁.getD i d := by
  obtain ⟨t, rfl⟩ := h
  exact List.getD_append _ _ _ _ hi

theorem run_getD {α : Type} (F : Gate → List α → α) (init : List α) (gs : List Gate) {i : ℕ}
    (hi : i < init.length) (d : α) : (run F init gs).getD i d = init.getD i d :=
  getD_of_prefix (run_prefix F gs init) hi d

theorem getD_at {α : Type} {l : List α} {x d : α} {n : ℕ} (h : n = l.length) :
    (l ++ [x]).getD n d = x := by
  subst h; rw [List.getD_append_right _ _ _ _ (le_refl _)]; simp

theorem getD_pre {α : Type} {l : List α} {x d : α} {n : ℕ} (h : n < l.length) :
    (l ++ [x]).getD n d = l.getD n d := List.getD_append _ _ _ _ h

theorem getD_last {α : Type} (l : List α) (x d : α) : (l ++ [x]).getD l.length d = x := by
  rw [List.getD_append_right _ _ _ _ (le_refl _)]; simp

def wF : Gate → List Bool → Bool := fun g w => g.op.eval (g.inputs.map fun i => w.getD i false)

def dF : Gate → List ℕ → ℕ := fun g ts => 1 + g.inputs.foldl (fun m j => max m (ts.getD j 0)) 0

def RB (p : ℕ) (gs : List Gate) : Prop :=
  ∀ j < gs.length, ∀ i ∈ (gs.getD j ⟨GateOp.or, []⟩).inputs, i < p + j

theorem RB_nil (p : ℕ) : RB p [] := by
  intro j hj; simp at hj

theorem RB_append {p : ℕ} {gs hs : List Gate} (h1 : RB p gs) (h2 : RB (p + gs.length) hs) :
    RB p (gs ++ hs) := by
  intro j hj i hi
  by_cases hj' : j < gs.length
  · rw [List.getD_append _ _ _ _ hj'] at hi
    exact h1 j hj' i hi
  · rw [List.getD_append_right _ _ _ _ (by omega)] at hi
    simp only [List.length_append] at hj
    have := h2 (j - gs.length) (by omega) i hi
    omega

theorem RB_single {p : ℕ} {g : Gate} (h : ∀ i ∈ g.inputs, i < p) : RB p [g] := by
  intro j hj i hi
  simp at hj; subst hj
  simpa using h i (by simpa using hi)

def tree : ℕ → (ℕ → ℕ) → ℕ → ℕ → List Gate × ℕ
  | 0, f, _, _ => ([], f 0)
  | d+1, f, m, p =>
    if m ≤ 2^d then tree d f m p else
    (((tree d f (2^d) p).1 ++ (tree d (fun i => f (2^d + i)) (m - 2^d) (p + (tree d f (2^d) p).1.length)).1)
      ++ [⟨GateOp.and, [(tree d f (2^d) p).2,
        (tree d (fun i => f (2^d + i)) (m - 2^d) (p + (tree d f (2^d) p).1.length)).2]⟩],
     p + (tree d f (2^d) p).1.length +
       (tree d (fun i => f (2^d + i)) (m - 2^d) (p + (tree d f (2^d) p).1.length)).1.length)

def TreeSpec (d : ℕ) (f : ℕ → ℕ) (m p : ℕ) (T : List Gate × ℕ) : Prop :=
  T.1.length = m - 1 ∧ T.2 < p + T.1.length ∧ RB p T.1 ∧
  (∀ g ∈ T.1, g.op = GateOp.and ∧ g.inputs.length = 2) ∧
  (∀ ts : List Bool, ts.length = p →
    ((run wF ts T.1).getD T.2 false = true ↔ ∀ i < m, ts.getD (f i) false = true)) ∧
  (∀ (ts : List ℕ) (c : ℕ), ts.length = p → (∀ i < m, ts.getD (f i) 0 ≤ c) →
    (run dF ts T.1).getD T.2 0 ≤ c + d)

theorem tree_spec (d : ℕ) : ∀ (f : ℕ → ℕ) (m p : ℕ), 1 ≤ m → m ≤ 2^d → (∀ i < m, f i < p) →
    TreeSpec d f m p (tree d f m p) := by
  induction d with
  | zero =>
    intro f m p h1 h2 hf
    have hm : m = 1 := by simp at h2; omega
    subst hm
    refine ⟨rfl, ?_, RB_nil p, by simp [tree], ?_, ?_⟩
    · simpa [tree] using hf 0 (by omega)
    · intro ts _
      simp only [tree, run, List.foldl_nil]
      constructor
      · intro h i hi; have : i = 0 := by omega
        subst this; exact h
      · intro h; exact h 0 (by omega)
    · intro ts c _ hc
      simpa [tree, run] using hc 0 (by omega)
  | succ d ih =>
    intro f m p h1 h2 hf
    by_cases hm : m ≤ 2^d
    · have := ih f m p h1 hm hf
      simp only [tree, hm, ite_true]
      obtain ⟨a, b, c, e, g, k⟩ := this
      refine ⟨a, b, c, e, g, ?_⟩
      intro ts c' hl hc
      have := k ts c' hl hc
      omega
    · have hpos : 1 ≤ 2^d := Nat.one_le_two_pow
      have hA := ih f (2^d) p hpos (le_refl _) (fun i hi => hf i (by omega))
      set A := tree d f (2^d) p with hAdef
      have hB := ih (fun i => f (2^d + i)) (m - 2^d) (p + A.1.length) (by omega)
        (by rw [pow_succ] at h2; omega) (fun i hi => by have := hf (2^d + i) (by omega); omega)
      set B := tree d (fun i => f (2^d + i)) (m - 2^d) (p + A.1.length) with hBdef
      have ht : tree (d+1) f m p = ((A.1 ++ B.1) ++ [⟨GateOp.and, [A.2, B.2]⟩],
          p + A.1.length + B.1.length) := by
        simp only [tree, hm, ite_false, hAdef, hBdef]
      rw [ht]
      obtain ⟨a1, a2, a3, a4, a5, a6⟩ := hA
      obtain ⟨b1, b2, b3, b4, b5, b6⟩ := hB
      refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
      · simp only [List.length_append, List.length_singleton, a1, b1]; omega
      · simp; omega
      · refine RB_append (RB_append a3 b3) (RB_single ?_)
        intro i hi
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
        simp only [List.length_append]
        rcases hi with h | h <;> rw [h] <;> omega
      · intro g hg
        simp only [List.mem_append, List.mem_singleton] at hg
        rcases hg with (hg | hg) | rfl
        · exact a4 g hg
        · exact b4 g hg
        · simp
      · intro ts hl
        have lA : (run wF ts A.1).length = p + A.1.length := by rw [run_length, hl]
        have lB : (run wF (run wF ts A.1) B.1).length = p + A.1.length + B.1.length := by
          rw [run_length, lA]
        rw [run_append, run_append, run_single, ← lB, getD_last]
        have eA : (run wF (run wF ts A.1) B.1).getD A.2 false = (run wF ts A.1).getD A.2 false :=
          run_getD _ _ _ (by rw [lA]; exact a2) _
        simp only [wF, GateOp.eval, List.map_cons, List.map_nil, List.all_cons, List.all_nil,
          id, Bool.and_true, Bool.and_eq_true]
        rw [eA, a5 ts hl, b5 _ lA]
        constructor
        · rintro ⟨hx, hy⟩ i hi
          by_cases hi' : i < 2^d
          · exact hx i hi'
          · have := hy (i - 2^d) (by omega)
            rw [run_getD _ _ _ (by rw [hl]; exact hf _ (by omega))] at this
            simpa [show 2^d + (i - 2^d) = i by omega] using this
        · intro h
          refine ⟨fun i hi => h i (by omega), fun i hi => ?_⟩
          rw [run_getD _ _ _ (by rw [hl]; exact hf _ (by omega))]
          exact h _ (by omega)
      · intro ts c hl hc
        have lA : (run dF ts A.1).length = p + A.1.length := by rw [run_length, hl]
        have lB : (run dF (run dF ts A.1) B.1).length = p + A.1.length + B.1.length := by
          rw [run_length, lA]
        rw [run_append, run_append, run_single, ← lB, getD_last]
        have eA : (run dF (run dF ts A.1) B.1).getD A.2 0 = (run dF ts A.1).getD A.2 0 :=
          run_getD _ _ _ (by rw [lA]; exact a2) _
        simp only [dF, List.foldl_cons, List.foldl_nil]
        rw [eA]
        have x1 := a6 ts c hl (fun i hi => hc i (by omega))
        have x2 := b6 (run dF ts A.1) c lA (fun i hi => by
          rw [run_getD _ _ _ (by rw [hl]; exact hf _ (by omega))]
          exact hc _ (by omega))
        omega

def blk (s j : ℕ) : List Gate :=
  [⟨GateOp.and, [j, 2*s+j]⟩, ⟨GateOp.and, [s+j, 3*s+j]⟩, ⟨GateOp.or, [4*s+2+3*j, 4*s+2+3*j+1]⟩]

def P (s k : ℕ) : List Gate := (List.range k).flatMap (blk s)

theorem P_succ (s k : ℕ) : P s (k+1) = P s k ++ blk s k := by
  simp [P, List.range_succ, List.flatMap_append]

theorem P_length (s k : ℕ) : (P s k).length = 3*k := by
  induction k with
  | zero => simp [P]
  | succ k ih => rw [P_succ, List.length_append, ih]; simp [blk]; ring

theorem P_gates (s k : ℕ) : ∀ g ∈ P s k, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length = 2 := by
  intro g hg
  simp only [P, List.mem_flatMap, blk] at hg
  obtain ⟨j, _, hg⟩ := hg
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl <;> simp

theorem P_RB (s k : ℕ) (hk : k ≤ s) : RB (4*s+2) (P s k) := by
  induction k with
  | zero => exact RB_nil _
  | succ k ih =>
    rw [P_succ]
    refine RB_append (ih (by omega)) ?_
    rw [P_length]
    intro j hj i hi
    simp only [blk, List.length_cons, List.length_nil] at hj
    interval_cases j <;> simp [blk] at hi <;> omega

theorem blk_eval {α : Type} (F : Gate → List α → α) (s j : ℕ) (R : List α) (d : α)
    (h : R.length = 4*s+2+3*j) :
    (run F R (blk s j)).getD (4*s+2+3*j+2) d =
      F ⟨GateOp.or, [4*s+2+3*j, 4*s+2+3*j+1]⟩ ((R ++ [F ⟨GateOp.and, [j, 2*s+j]⟩ R]) ++
        [F ⟨GateOp.and, [s+j, 3*s+j]⟩ (R ++ [F ⟨GateOp.and, [j, 2*s+j]⟩ R])]) := by
  simp only [blk, run, List.foldl_cons, List.foldl_nil]
  exact getD_at (by simp [h])

theorem P_wires (s k : ℕ) (hk : k ≤ s) (ts : List Bool) (hl : ts.length = 4*s+2) :
    ∀ j < k, (run wF ts (P s k)).getD (4*s+2+3*j+2) false =
      ((ts.getD j false && ts.getD (2*s+j) false) || (ts.getD (s+j) false && ts.getD (3*s+j) false)) := by
  induction k with
  | zero => intro j hj; omega
  | succ k ih =>
    intro j hj
    have lR : (run wF ts (P s k)).length = 4*s+2+3*k := by rw [run_length, hl, P_length]
    rw [P_succ, run_append]
    by_cases hjk : j < k
    · rw [run_getD _ _ _ (by rw [lR]; omega)]
      exact ih (by omega) j hjk
    · have hj' : j = k := by omega
      subst hj'
      set R := run wF ts (P s j) with hR
      have e : ∀ i < ts.length, R.getD i false = ts.getD i false := fun i hi =>
        run_getD _ _ _ hi _
      rw [blk_eval _ _ _ _ _ lR]
      simp only [wF, List.map_cons, List.map_nil]
      rw [getD_pre (by simp [lR]), getD_at (by simp [lR]), getD_at (by simp [lR])]
      repeat rw [getD_pre (by simp [lR]; omega)]
      rw [e j (by omega), e (2*s+j) (by omega), e (s+j) (by omega), e (3*s+j) (by omega)]
      simp [GateOp.eval]

theorem P_depth (s k : ℕ) (hk : k ≤ s) :
    ∀ j < k, (run dF (List.replicate (4*s+2) 0) (P s k)).getD (4*s+2+3*j+2) 0 ≤ 2 := by
  induction k with
  | zero => intro j hj; omega
  | succ k ih =>
    intro j hj
    have lR : (run dF (List.replicate (4*s+2) 0) (P s k)).length = 4*s+2+3*k := by
      rw [run_length, List.length_replicate, P_length]
    rw [P_succ, run_append]
    by_cases hjk : j < k
    · rw [run_getD _ _ _ (by rw [lR]; omega)]
      exact ih (by omega) j hjk
    · have hj' : j = k := by omega
      subst hj'
      set R := run dF (List.replicate (4*s+2) 0) (P s j) with hR
      have e : ∀ i < 4*s+2, R.getD i 0 = 0 := fun i hi => by
        rw [hR, run_getD _ _ _ (by simpa using hi)]; simp [hi]
      rw [blk_eval _ _ _ _ _ lR]
      simp only [dF, List.foldl_cons, List.foldl_nil]
      rw [getD_pre (by simp [lR]), getD_at (by simp [lR]), getD_at (by simp [lR])]
      repeat rw [getD_pre (by simp [lR]; omega)]
      rw [e j (by omega), e (2*s+j) (by omega), e (s+j) (by omega), e (3*s+j) (by omega)]
      simp

theorem inp_len (s : ℕ) (u v w z : Fin s → Bool) :
    (List.ofFn u ++ List.ofFn v ++ List.ofFn w ++ List.ofFn z ++ [false, true]).length = 4*s+2 := by
  simp; ring

theorem inp_get (s : ℕ) (u v w z : Fin s → Bool) (i : ℕ) (h : i < s) :
    (List.ofFn u ++ List.ofFn v ++ List.ofFn w ++ List.ofFn z ++ [false, true]).getD i false = u ⟨i, h⟩ ∧
    (List.ofFn u ++ List.ofFn v ++ List.ofFn w ++ List.ofFn z ++ [false, true]).getD (s+i) false = v ⟨i, h⟩ ∧
    (List.ofFn u ++ List.ofFn v ++ List.ofFn w ++ List.ofFn z ++ [false, true]).getD (2*s+i) false = w ⟨i, h⟩ ∧
    (List.ofFn u ++ List.ofFn v ++ List.ofFn w ++ List.ofFn z ++ [false, true]).getD (3*s+i) false = z ⟨i, h⟩ := by
  simp only [List.append_assoc]
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [List.getD_append _ _ _ _ (by simpa using h)]; simp [List.getD_eq_getElem?_getD, h]
  · rw [List.getD_append_right _ _ _ _ (by simp), List.getD_append _ _ _ _ (by simp; omega)]
    simp [List.getD_eq_getElem?_getD, h]
  · rw [List.getD_append_right _ _ _ _ (by simp; omega), List.getD_append_right _ _ _ _ (by simp; omega),
      List.getD_append _ _ _ _ (by simp; omega)]
    simp [List.getD_eq_getElem?_getD]
    rw [dite_eq_left_of_eq_true (eq_true (by omega))]
    exact congrArg _ (Fin.ext (by dsimp only; omega))
  · rw [List.getD_append_right _ _ _ _ (by simp; omega), List.getD_append_right _ _ _ _ (by simp; omega),
      List.getD_append_right _ _ _ _ (by simp; omega), List.getD_append _ _ _ _ (by simp; omega)]
    simp [List.getD_eq_getElem?_getD]
    rw [dite_eq_left_of_eq_true (eq_true (by omega))]
    exact congrArg _ (Fin.ext (by dsimp only; omega))

theorem accepts_univ (s : ℕ) (L R : Finset (Fin s) × Finset (Fin s)) :
    (∃ Z : Finset (Fin s), (Z ⊆ L.2 ∧ ∀ j, j ∉ Z → j ∈ L.1) ∧ (Z ⊆ R.2 ∧ ∀ j, j ∉ Z → j ∈ R.1)) ↔
    ∀ j : Fin s, (j ∈ L.1 ∧ j ∈ R.1) ∨ (j ∈ L.2 ∧ j ∈ R.2) := by
  classical
  constructor
  · rintro ⟨Z, ⟨h1, h2⟩, ⟨h3, h4⟩⟩ j
    by_cases hj : j ∈ Z
    · exact Or.inr ⟨h1 hj, h3 hj⟩
    · exact Or.inl ⟨h2 j hj, h4 j hj⟩
  · intro h
    refine ⟨Finset.univ.filter (fun j => j ∈ L.2 ∧ j ∈ R.2), ⟨?_, ?_⟩, ⟨?_, ?_⟩⟩
    · intro j hj; simp at hj; exact hj.1
    · intro j hj; simp at hj; rcases h j with h' | h'
      · exact h'.1
      · exact absurd h'.2 (hj h'.1)
    · intro j hj; simp at hj; exact hj.2
    · intro j hj; simp at hj; rcases h j with h' | h'
      · exact h'.2
      · exact absurd h'.2 (hj h'.1)

theorem compat_single {s : ℕ} (Y Z : Finset (Fin s)) (h1 : Y ⊆ Z)
    (h2 : ∀ j, j ∉ Y → j ∉ Z) : Y = Z := by
  apply Finset.Subset.antisymm h1
  intro j hj
  by_contra hY
  exact h2 j hY hj

end PEqualNP.Outside.L_lib_1478

theorem PEqualNP.Outside.L_lib_1478 : letI : ∀ Q : Prop, Decidable Q := Classical.propDecidable
let valid := fun (h : Nat) (D : PEqualNP.CircuitLowerBounds.Circuit) => PEqualNP.MetaComplexity.FanInTwo D ∧
  PEqualNP.MetaComplexity.NestedCover.ReadsBack (h+2) D ∧ D.output < h+2+D.size
let pos := fun (h : Nat) (D : PEqualNP.CircuitLowerBounds.Circuit) => valid h D ∧ PEqualNP.NotBracket.notCount D=0
let depths := fun (h : Nat) (D : PEqualNP.CircuitLowerBounds.Circuit) =>
  D.gates.foldl (fun (ts : List Nat) g =>
    ts ++ [1+g.inputs.foldl (fun m j => max m (ts.getD j 0)) 0]) (List.replicate (h+2) 0)
∀ s : Nat,
  let V := Finset (Fin s)
  let compat := fun (Z : V) (L : V × V) => Z ⊆ L.2 ∧ Finset.univ \ Z ⊆ L.1
  let accepts := fun (W : Finset V) (L R : V × V) => ∃ Z ∈ W, compat Z L ∧ compat Z R
  let input := fun (L R : V × V) =>
    List.ofFn (fun j : Fin s => decide (j ∈ L.1)) ++ List.ofFn (fun j : Fin s => decide (j ∈ L.2)) ++
    List.ofFn (fun j : Fin s => decide (j ∈ R.1)) ++ List.ofFn (fun j : Fin s => decide (j ∈ R.2)) ++ [false,true]
  (∀ (W : Finset V) (r : Nat),
    (∃ a b : Fin r → V × V → Prop,
      ∀ L R : V × V, accepts W L R ↔ ∃ i : Fin r, a i L ∧ b i R) ↔ W.card ≤ r) ∧
  ∃ E : PEqualNP.CircuitLowerBounds.Circuit, pos (4*s) E ∧ E.size ≤ 4*s ∧
    (depths (4*s) E).getD E.output 0 ≤ Nat.clog 2 (max 1 s)+2 ∧
    ∀ L R : V × V, (E.wires (input L R)).getD E.output false=true ↔ accepts Finset.univ L R := by
  intro valid pos depths s V compat accepts input
  have compat_iff : ∀ Z L, compat Z L ↔ (Z ⊆ L.2 ∧ ∀ j, j ∉ Z → j ∈ L.1) := by
    intro Z L
    show (Z ⊆ L.2 ∧ _ ⊆ L.1) ↔ _
    constructor
    · rintro ⟨h1, h2⟩
      exact ⟨h1, fun j hj => h2 (by simp [Finset.mem_sdiff, hj])⟩
    · rintro ⟨h1, h2⟩
      exact ⟨h1, fun j hj => h2 j (by simp [Finset.mem_sdiff] at hj; exact hj)⟩
  refine ⟨?_, ?_⟩
  · intro W r
    constructor
    · rintro ⟨a, b, hab⟩
      have cZ : ∀ Z : V, compat Z (Finset.univ \ Z, Z) := fun Z =>
        (compat_iff _ _).2 ⟨subset_refl _, fun j hj => Finset.mem_sdiff.2 ⟨Finset.mem_univ _, hj⟩⟩
      have key : ∀ Z ∈ W, ∃ i : Fin r, a i (Finset.univ \ Z, Z) ∧ b i (Finset.univ \ Z, Z) :=
        fun Z hZ => (hab _ _).1 ⟨Z, hZ, cZ Z, cZ Z⟩
      rcases W.eq_empty_or_nonempty with hW | ⟨Z0, hZ0⟩
      · rw [hW]; simp
      have : Nonempty (Fin r) := ⟨(key Z0 hZ0).choose⟩
      choose! g hg using key
      have uniq : ∀ Y Z : V, compat Y (Finset.univ \ Z, Z) → Y = Z := by
        intro Y Z h
        rw [compat_iff] at h
        refine PEqualNP.Outside.L_lib_1478.compat_single Y Z h.1 (fun j hj => ?_)
        exact (Finset.mem_sdiff.1 (h.2 j hj)).2
      have inj : Set.InjOn g W := by
        intro Z hZ Z' hZ' he
        have hacc : accepts W (Finset.univ \ Z, Z) (Finset.univ \ Z', Z') :=
          (hab _ _).2 ⟨g Z, (hg Z hZ).1, he ▸ (hg Z' hZ').2⟩
        obtain ⟨Y, _, c1, c2⟩ := hacc
        rw [← uniq Y Z c1, ← uniq Y Z' c2]
      calc W.card ≤ (Finset.univ : Finset (Fin r)).card :=
            Finset.card_le_card_of_injOn g (fun _ _ => Finset.mem_coe.2 (Finset.mem_univ _)) inj
        _ = r := by simp
    · intro hcard
      refine ⟨fun i L => ∃ Z, W.toList[i.val]? = some Z ∧ compat Z L,
        fun i R => ∃ Z, W.toList[i.val]? = some Z ∧ compat Z R, ?_⟩
      intro L R
      constructor
      · rintro ⟨Z, hZ, c1, c2⟩
        obtain ⟨n, hn, hnZ⟩ := List.getElem_of_mem (Finset.mem_toList.2 hZ)
        have hr : n < r := by rw [Finset.length_toList] at hn; omega
        exact ⟨⟨n, hr⟩, ⟨Z, by rw [List.getElem?_eq_getElem hn, hnZ], c1⟩, ⟨Z, by rw [List.getElem?_eq_getElem hn, hnZ], c2⟩⟩
      · rintro ⟨i, ⟨Z, h1, c1⟩, ⟨Z', h2, c2⟩⟩
        have : Z = Z' := by rw [h1] at h2; exact Option.some.inj h2
        subst this
        exact ⟨Z, Finset.mem_toList.1 (List.mem_of_getElem? h1), c1, c2⟩
  · have acc_iff : ∀ L R : V × V, accepts Finset.univ L R ↔
        ∀ j : Fin s, (j ∈ L.1 ∧ j ∈ R.1) ∨ (j ∈ L.2 ∧ j ∈ R.2) := by
      intro L R
      rw [← PEqualNP.Outside.L_lib_1478.accepts_univ]
      constructor
      · rintro ⟨Z, _, c1, c2⟩
        exact ⟨Z, (compat_iff _ _).1 c1, (compat_iff _ _).1 c2⟩
      · rintro ⟨Z, c1, c2⟩
        exact ⟨Z, Finset.mem_univ _, (compat_iff _ _).2 c1, (compat_iff _ _).2 c2⟩
    rcases Nat.eq_zero_or_pos s with hs | hs
    · refine ⟨⟨[], 1⟩, ⟨⟨?_, ?_, ?_⟩, ?_⟩, ?_, ?_, ?_⟩
      · intro g hg; simp at hg
      · intro j hj; simp at hj
      · simp [CircuitLowerBounds.Circuit.size]
      · simp [NotBracket.notCount]
      · simp [CircuitLowerBounds.Circuit.size]
      · show (List.replicate (4*s+2) 0).getD 1 0 ≤ _
        simp
      · intro L R
        rw [acc_iff]
        subst hs
        constructor
        · intro _ j; exact j.elim0
        · intro _; rfl
    · open PEqualNP.Outside.L_lib_1478 in
      obtain ⟨t1, t2, t3, t4, t5, t6⟩ := tree_spec (Nat.clog 2 s) (fun i => 4*s+2+3*i+2) s (4*s+2+3*s) hs
        (Nat.le_pow_clog one_lt_two s) (fun i hi => by omega)
      set T := tree (Nat.clog 2 s) (fun i => 4*s+2+3*i+2) s (4*s+2+3*s) with hT
      have gl : (P s s ++ T.1).length = 3*s + (s-1) := by simp [P_length, t1]
      refine ⟨⟨P s s ++ T.1, T.2⟩, ⟨⟨?_, ?_, ?_⟩, ?_⟩, ?_, ?_, ?_⟩
      · intro g hg
        simp only [List.mem_append] at hg
        rcases hg with hg | hg
        · obtain ⟨h1, h2⟩ := P_gates s s g hg
          refine ⟨?_, by omega⟩
          rcases h1 with h1 | h1 <;> simp [h1]
        · obtain ⟨h1, h2⟩ := t4 g hg
          exact ⟨by simp [h1], by omega⟩
      · show RB (4*s+2) (P s s ++ T.1)
        exact RB_append (P_RB s s le_rfl) (by rw [P_length]; exact t3)
      · show T.2 < 4*s+2+(P s s ++ T.1).length
        rw [List.length_append, P_length]; omega
      · simp only [NotBracket.notCount, List.length_eq_zero_iff, List.filter_eq_nil_iff]
        intro g hg
        simp only [List.mem_append] at hg
        rcases hg with hg | hg
        · rcases (P_gates s s g hg).1 with h1 | h1 <;> simp [h1]
        · simp [(t4 g hg).1]
      · show (P s s ++ T.1).length ≤ 4*s
        rw [gl]; omega
      · show (run dF (List.replicate (4*s+2) 0) (P s s ++ T.1)).getD T.2 0 ≤ _
        rw [run_append, max_eq_right hs]
        have := t6 (run dF (List.replicate (4*s+2) 0) (P s s)) 2
          (by rw [run_length, List.length_replicate, P_length])
          (fun i hi => P_depth s s le_rfl i hi)
        omega
      · intro L R
        rw [acc_iff]
        show (run wF (input L R) (P s s ++ T.1)).getD T.2 false = true ↔ _
        have hl : (input L R).length = 4*s+2 := inp_len s _ _ _ _
        rw [run_append, t5 _ (by rw [run_length, hl, P_length])]
        constructor
        · intro h j
          have := h j.val j.isLt
          rw [P_wires s s le_rfl _ hl j.val j.isLt] at this
          simp only [input] at this
          rw [(inp_get s _ _ _ _ j.val j.isLt).1, (inp_get s _ _ _ _ j.val j.isLt).2.1,
            (inp_get s _ _ _ _ j.val j.isLt).2.2.1, (inp_get s _ _ _ _ j.val j.isLt).2.2.2] at this
          simpa using this
        · intro h i hi
          rw [P_wires s s le_rfl _ hl i hi]
          simp only [input]
          rw [(inp_get s _ _ _ _ i hi).1, (inp_get s _ _ _ _ i hi).2.1,
            (inp_get s _ _ _ _ i hi).2.2.1, (inp_get s _ _ _ _ i hi).2.2.2]
          simpa using h ⟨i, hi⟩
