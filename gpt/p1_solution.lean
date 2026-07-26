import Mathlib
set_option backward.isDefEq.respectTransparency false

/-- A *board* is a finite multiset of natural numbers.  The full board discipline
(entries `≥ 1`, cardinality `2026`) is captured by the predicate `IsInitial`. -/
abbrev Board := Multiset ℕ

/-- An *initial board*: exactly `2026` entries, each strictly greater than `1`. -/
def IsInitial (B : Board) : Prop :=
  Multiset.card B = 2026 ∧ ∀ a ∈ B, 1 < a

/-- A single *move*: pick two entries `m, n` (from two distinct positions,
modelled as two separate elements of the multiset) both `> 1`, remove them and
insert `gcd(m, n)` and `lcm(m, n) / gcd(m, n)`.  Using `m ::ₘ n ::ₘ s` for the
source board automatically encodes that the two chosen positions are distinct
(they are two separate multiset elements, whose *values* may coincide). -/
def Move (B B' : Board) : Prop :=
  ∃ (m n : ℕ) (s : Board), 1 < m ∧ 1 < n ∧
    B = m ::ₘ n ::ₘ s ∧
    B' = Nat.gcd m n ::ₘ (Nat.lcm m n / Nat.gcd m n) ::ₘ s

/-- A board is *terminal* when at most one entry is `> 1`, so no move is possible. -/
def IsTerminal (B : Board) : Prop :=
  Multiset.card (B.filter (fun a => 1 < a)) ≤ 1

/-- A board has a *unique large entry* when exactly one entry is `> 1`. -/
def HasUniqueLarge (B : Board) : Prop :=
  Multiset.card (B.filter (fun a => 1 < a)) = 1

/-- `Reachable B B'` : `B'` can be obtained from `B` by a finite sequence of moves
(the reflexive–transitive closure of `Move`).  A finite play from `B` to a
terminal board `B'` is precisely a witness of `Reachable B B'` with `IsTerminal B'`. -/
def Reachable (B B' : Board) : Prop := Relation.ReflTransGen Move B B'

/-- The exponent `g_p` for a prime `p` and board `B`: the `gcd` of the `p`-adic
valuations of the entries of `B`.  Since `gcd(a, 0) = a`, valuations equal to `0`
(entries not divisible by `p`) do not affect this gcd, so `gExp p B` is the gcd of
the *positive* `p`-adic valuations occurring in `B`. -/
noncomputable def gExp (p : ℕ) (B : Board) : ℕ :=
  (B.map (fun a => padicValNat p a)).gcd

/-- The claimed invariant terminal value
`M = ∏_{p ∣ ∏ B} p ^ gExp p B`, the product over all primes dividing some entry
of `B` of `p` raised to the gcd of the `p`-adic valuations. -/
noncomputable def Mval (B : Board) : ℕ :=
  ∏ p ∈ B.prod.primeFactors, p ^ gExp p B

/-! The following helpers record the two elementary invariants used below. -/

def PositiveBoard (B : Board) : Prop := ∀ a ∈ B, 0 < a

def boardRank (B : Board) : ℕ × ℕ :=
  (B.prod, (B.filter (fun a => 1 < a)).card)

lemma move_preserves_positive {B B' : Board} (hB : PositiveBoard B) (hmove : Move B B') :
    PositiveBoard B' := by
  rcases hmove with ⟨m, n, s, hm, hn, rfl, rfl⟩
  have hm0 : 0 < m := by omega
  have hn0 : 0 < n := by omega
  have hg0 : 0 < Nat.gcd m n := Nat.gcd_pos_of_pos_left n hm0
  have hl0 : 0 < Nat.lcm m n := Nat.lcm_pos hm0 hn0
  have hgl : Nat.gcd m n ∣ Nat.lcm m n :=
    dvd_trans (Nat.gcd_dvd_left m n) (Nat.dvd_lcm_left m n)
  have hq0 : 0 < Nat.lcm m n / Nat.gcd m n :=
    Nat.div_pos (Nat.le_of_dvd hl0 hgl) hg0
  intro a ha
  simp only [Multiset.mem_cons] at ha
  rcases ha with rfl | rfl | ha
  · exact hg0
  · exact hq0
  · exact hB a (by simp [ha])

lemma move_rank_decreases {B B' : Board} (hB : PositiveBoard B) (hmove : Move B B') :
    Prod.Lex (· < ·) (· < ·) (boardRank B') (boardRank B) := by
  rcases hmove with ⟨m, n, s, hm, hn, rfl, rfl⟩
  have hs : PositiveBoard s := by
    intro a ha
    exact hB a (by simp [ha])
  have hsprod : 0 < s.prod := Multiset.prod_pos hs
  have hm0 : 0 < m := by omega
  have hn0 : 0 < n := by omega
  have hl0 : 0 < Nat.lcm m n := Nat.lcm_pos hm0 hn0
  have hgl : Nat.gcd m n ∣ Nat.lcm m n :=
    dvd_trans (Nat.gcd_dvd_left m n) (Nat.dvd_lcm_left m n)
  by_cases hg : Nat.gcd m n = 1
  · have hprod :
        Nat.gcd m n * (Nat.lcm m n / Nat.gcd m n * s.prod) = m * (n * s.prod) := by
      calc
        Nat.gcd m n * (Nat.lcm m n / Nat.gcd m n * s.prod) =
            (Nat.gcd m n * (Nat.lcm m n / Nat.gcd m n)) * s.prod := by ac_rfl
        _ = Nat.lcm m n * s.prod := by rw [Nat.mul_div_cancel' hgl]
        _ = m * n * s.prod := by rw [← Nat.gcd_mul_lcm m n, hg]; simp
        _ = m * (n * s.prod) := by ac_rfl
    simp only [boardRank, Multiset.prod_cons]
    rw [hprod]
    apply Prod.Lex.right
    have hl : 1 < Nat.lcm m n :=
      lt_of_lt_of_le hm (Nat.le_of_dvd hl0 (Nat.dvd_lcm_left m n))
    simp [hm, hn, hg, hl]
  · apply Prod.Lex.left
    simp only [Multiset.prod_cons]
    have hg1 : 1 < Nat.gcd m n := by
      have hg0 := Nat.gcd_pos_of_pos_left n hm0
      omega
    have hl_lt : Nat.lcm m n < m * n := by
      calc
        Nat.lcm m n = 1 * Nat.lcm m n := by simp
        _ < Nat.gcd m n * Nat.lcm m n := by
          exact (Nat.mul_lt_mul_right hl0).2 hg1
        _ = m * n := Nat.gcd_mul_lcm m n
    calc
      Nat.gcd m n * (Nat.lcm m n / Nat.gcd m n * s.prod) =
          (Nat.gcd m n * (Nat.lcm m n / Nat.gcd m n)) * s.prod := by ac_rfl
      _ = Nat.lcm m n * s.prod := by rw [Nat.mul_div_cancel' hgl]
      _ < (m * n) * s.prod := (Nat.mul_lt_mul_right hsprod).2 hl_lt
      _ = m * (n * s.prod) := by ac_rfl

lemma initial_positive {B : Board} (hB : IsInitial B) : PositiveBoard B := by
  intro a ha
  exact lt_trans Nat.zero_lt_one (hB.2 a ha)

lemma reachable_positive {B B' : Board} (hB : PositiveBoard B) (hreach : Reachable B B') :
    PositiveBoard B' := by
  induction hreach with
  | refl => exact hB
  | tail hreach hmove ih => exact move_preserves_positive ih hmove

def HasLarge (B : Board) : Prop := ∃ a ∈ B, 1 < a

lemma initial_hasLarge {B : Board} (hB : IsInitial B) : HasLarge B := by
  have hne : B ≠ 0 := by
    intro h
    rw [h] at hB
    norm_num [IsInitial] at hB
  obtain ⟨a, ha⟩ := Multiset.exists_mem_of_ne_zero hne
  exact ⟨a, ha, hB.2 a ha⟩

lemma move_preserves_hasLarge {B B' : Board} (hmove : Move B B') : HasLarge B' := by
  rcases hmove with ⟨m, n, s, hm, hn, rfl, rfl⟩
  have hm0 : 0 < m := by omega
  have hn0 : 0 < n := by omega
  have hg0 : 0 < Nat.gcd m n := Nat.gcd_pos_of_pos_left n hm0
  by_cases hg : Nat.gcd m n = 1
  · have hl0 : 0 < Nat.lcm m n := Nat.lcm_pos hm0 hn0
    have hl : 1 < Nat.lcm m n :=
      lt_of_lt_of_le hm (Nat.le_of_dvd hl0 (Nat.dvd_lcm_left m n))
    exact ⟨Nat.lcm m n / Nat.gcd m n, by simp, by simpa [hg] using hl⟩
  · have hg1 : 1 < Nat.gcd m n := by omega
    exact ⟨Nat.gcd m n, by simp, hg1⟩

lemma reachable_hasLarge {B B' : Board} (hB : HasLarge B) (hreach : Reachable B B') :
    HasLarge B' := by
  induction hreach with
  | refl => exact hB
  | tail hreach hmove ih => exact move_preserves_hasLarge hmove

lemma gcd_min_max_sub (a b : ℕ) :
    Nat.gcd (min a b) (max a b - min a b) = Nat.gcd a b := by
  rcases le_total a b with hab | hba
  · simp [min_eq_left hab, max_eq_right hab, Nat.gcd_sub_self_right hab]
  · simp [min_eq_right hba, max_eq_left hba, Nat.gcd_sub_self_right hba, Nat.gcd_comm]

lemma gcdMonoid_min_max_sub (a b : ℕ) :
    gcd (min a b) (max a b - min a b) = gcd a b := by
  change Nat.gcd (min a b) (max a b - min a b) = Nat.gcd a b
  exact gcd_min_max_sub a b

lemma padicValNat_gcd (p m n : ℕ) (hp : p.Prime) (hm : m ≠ 0) (hn : n ≠ 0) :
    padicValNat p (Nat.gcd m n) = min (padicValNat p m) (padicValNat p n) := by
  rw [← Nat.factorization_def (Nat.gcd m n) hp, Nat.factorization_gcd hm hn]
  simp [Nat.factorization_def _ hp]

lemma padicValNat_lcm_div_gcd (p m n : ℕ) (hp : p.Prime) (hm : m ≠ 0) (hn : n ≠ 0) :
    padicValNat p (Nat.lcm m n / Nat.gcd m n) =
      max (padicValNat p m) (padicValNat p n) -
        min (padicValNat p m) (padicValNat p n) := by
  have hdiv : Nat.gcd m n ∣ Nat.lcm m n :=
    dvd_trans (Nat.gcd_dvd_left m n) (Nat.dvd_lcm_left m n)
  rw [← Nat.factorization_def (Nat.lcm m n / Nat.gcd m n) hp,
    Nat.factorization_div hdiv, Nat.factorization_lcm hm hn, Nat.factorization_gcd hm hn]
  simp [Nat.factorization_def _ hp]

lemma move_gExp (p : ℕ) (hp : p.Prime) {B B' : Board} (hmove : Move B B') :
    gExp p B' = gExp p B := by
  rcases hmove with ⟨m, n, s, hm, hn, rfl, rfl⟩
  have hm0 : m ≠ 0 := by omega
  have hn0 : n ≠ 0 := by omega
  simp only [gExp, Multiset.map_cons, Multiset.gcd_cons]
  rw [padicValNat_gcd p m n hp hm0 hn0,
    padicValNat_lcm_div_gcd p m n hp hm0 hn0]
  rw [← gcd_assoc, gcdMonoid_min_max_sub, gcd_assoc]

lemma reachable_gExp (p : ℕ) (hp : p.Prime) {B B' : Board} (hreach : Reachable B B') :
    gExp p B' = gExp p B := by
  induction hreach with
  | refl => rfl
  | tail hreach hmove ih => exact (move_gExp p hp hmove).trans ih

lemma Nat.Prime.exists_mem_multiset_dvd_nat {p : ℕ} (hp : p.Prime) {B : Multiset ℕ}
    (hpd : p ∣ B.prod) : ∃ a ∈ B, p ∣ a := by
  induction B using Multiset.induction_on with
  | empty => simp [hp.not_dvd_one] at hpd
  | @cons a s ih =>
      rw [Multiset.prod_cons] at hpd
      rcases hp.dvd_mul.mp hpd with hpa | hps
      · exact ⟨a, by simp, hpa⟩
      · obtain ⟨b, hb, hpb⟩ := ih hps
        exact ⟨b, by simp [hb], hpb⟩

lemma gExp_ne_zero_iff_mem_primeFactors (p : ℕ) (hp : p.Prime) {B : Board}
    (hB : PositiveBoard B) : gExp p B ≠ 0 ↔ p ∈ B.prod.primeFactors := by
  letI : Fact p.Prime := ⟨hp⟩
  rw [gExp, Multiset.gcd_ne_zero_iff]
  constructor
  · rintro ⟨v, hv, hv0⟩
    rcases Multiset.mem_map.mp hv with ⟨a, ha, rfl⟩
    have ha0 : a ≠ 0 := ne_of_gt (hB a ha)
    have hpda : p ∣ a := (dvd_iff_padicValNat_ne_zero ha0).mpr hv0
    exact Nat.mem_primeFactors.mpr
      ⟨hp, dvd_trans hpda (Multiset.dvd_prod ha), ne_of_gt (Multiset.prod_pos hB)⟩
  · intro hmem
    have hpd : p ∣ B.prod := (Nat.mem_primeFactors.mp hmem).2.1
    obtain ⟨a, ha, hpda⟩ := hp.exists_mem_multiset_dvd_nat hpd
    have ha0 : a ≠ 0 := ne_of_gt (hB a ha)
    exact ⟨padicValNat p a, Multiset.mem_map.mpr ⟨a, ha, rfl⟩,
      (dvd_iff_padicValNat_ne_zero ha0).mp hpda⟩

lemma reachable_primeFactors {B B' : Board} (hB : PositiveBoard B)
    (hreach : Reachable B B') : B'.prod.primeFactors = B.prod.primeFactors := by
  have hB' : PositiveBoard B' := reachable_positive hB hreach
  ext p
  by_cases hp : p.Prime
  · constructor
    · intro hpB'
      have hnz : gExp p B' ≠ 0 :=
        (gExp_ne_zero_iff_mem_primeFactors p hp hB').mpr hpB'
      have hnz' : gExp p B ≠ 0 := by simpa [reachable_gExp p hp hreach] using hnz
      exact (gExp_ne_zero_iff_mem_primeFactors p hp hB).mp hnz'
    · intro hpB
      have hnz : gExp p B ≠ 0 :=
        (gExp_ne_zero_iff_mem_primeFactors p hp hB).mpr hpB
      have hnz' : gExp p B' ≠ 0 := by simpa [reachable_gExp p hp hreach] using hnz
      exact (gExp_ne_zero_iff_mem_primeFactors p hp hB').mp hnz'
  · simp [Nat.mem_primeFactors, hp]

lemma terminal_tail_all_one {M : ℕ} {s : Board} (hM : 1 < M)
    (hpos : PositiveBoard (M ::ₘ s)) (hterm : IsTerminal (M ::ₘ s)) :
    ∀ a ∈ s, a = 1 := by
  have hcard : (s.filter (fun a => 1 < a)).card = 0 := by
    have hc : 1 + (s.filter (fun a => 1 < a)).card ≤ 1 := by
      simpa [IsTerminal, hM] using hterm
    omega
  intro a ha
  have ha0 : 0 < a := hpos a (by simp [ha])
  have hnot : ¬1 < a := by
    intro ha1
    have hamem : a ∈ s.filter (fun x => 1 < x) := Multiset.mem_filter.mpr ⟨ha, ha1⟩
    have : 0 < (s.filter (fun x => 1 < x)).card := Multiset.card_pos.mpr <| by
      intro hz
      rw [hz] at hamem
      simp at hamem
    omega
  omega

lemma terminal_prod_eq {B : Board} (hpos : PositiveBoard B) (hterm : IsTerminal B)
    {M : ℕ} (hM : 1 < M) (hmem : M ∈ B) : B.prod = M := by
  obtain ⟨s, rfl⟩ := Multiset.exists_cons_of_mem hmem
  have hs := terminal_tail_all_one hM hpos hterm
  simp only [Multiset.prod_cons]
  have hsprod : s.prod = 1 := Multiset.prod_eq_one hs
  simp [hsprod]

lemma terminal_gExp_eq {B : Board} (hpos : PositiveBoard B) (hterm : IsTerminal B)
    {M : ℕ} (hM : 1 < M) (hmem : M ∈ B) (p : ℕ) :
    gExp p B = padicValNat p M := by
  obtain ⟨s, rfl⟩ := Multiset.exists_cons_of_mem hmem
  have hs := terminal_tail_all_one hM hpos hterm
  have hsgcd : (s.map (fun a => padicValNat p a)).gcd = 0 := by
    rw [Multiset.gcd_eq_zero_iff]
    intro v hv
    rcases Multiset.mem_map.mp hv with ⟨a, ha, rfl⟩
    rw [hs a ha]
    simp
  simp [gExp, hsgcd]

lemma terminal_value_formula (B₀ : Board) (hB₀ : IsInitial B₀)
    (B' : Board) (hreach : Reachable B₀ B') (hterm : IsTerminal B')
    (M : ℕ) (hM : 1 < M) (hmem : M ∈ B') :
    M = Mval B₀ := by
  have hpos0 : PositiveBoard B₀ := initial_positive hB₀
  have hpos' : PositiveBoard B' := reachable_positive hpos0 hreach
  have hprod : B'.prod = M := terminal_prod_eq hpos' hterm hM hmem
  have hpf' : B'.prod.primeFactors = B₀.prod.primeFactors :=
    reachable_primeFactors hpos0 hreach
  have hpf : B₀.prod.primeFactors = M.primeFactors := by
    rw [hprod] at hpf'
    exact hpf'.symm
  unfold Mval
  rw [hpf]
  calc
    M = ∏ p ∈ M.primeFactors, p ^ M.factorization p := by
      exact (Nat.prod_factorization_pow_eq_self (by omega)).symm
    _ = ∏ p ∈ M.primeFactors, p ^ gExp p B₀ := by
      apply Finset.prod_congr rfl
      intro p hp
      have hprime : p.Prime := Nat.prime_of_mem_primeFactors hp
      congr 1
      rw [Nat.factorization_def M hprime]
      exact (terminal_gExp_eq hpos' hterm hM hmem p).symm.trans
        (reachable_gExp p hprime hreach)

/-- **Statement (a), part 1 — termination.**  There is no infinite play starting
from an initial board `B₀`: no infinite sequence of boards can start at `B₀` and
have every consecutive pair related by a `Move`. -/
theorem statement_a_termination (B₀ : Board) (hB₀ : IsInitial B₀) :
    ¬ ∃ f : ℕ → Board, f 0 = B₀ ∧ ∀ k, Move (f k) (f (k + 1)) := by
  rintro ⟨f, hf0, hfmove⟩
  have hpos : ∀ k, PositiveBoard (f k) := by
    intro k
    induction k with
    | zero => simpa [hf0] using initial_positive hB₀
    | succ k ih => exact move_preserves_positive ih (by simpa [Nat.add_comm] using hfmove k)
  let g : ℕ → ℕ × ℕ := fun k => boardRank (f k)
  have hg : ∀ k, Prod.Lex (· < ·) (· < ·) (g (k + 1)) (g k) := by
    intro k
    exact move_rank_decreases (hpos k) (hfmove k)
  exact (wellFounded_iff_isEmpty_descending_chain.mp
    (Nat.lt_wfRel.wf.prod_lex Nat.lt_wfRel.wf)).false ⟨g, hg⟩

/-- **Statement (a), part 2 — unique large entry.**  Any terminal board reachable
from an initial board `B₀` has exactly one entry `> 1`. -/
theorem statement_a_unique_large (B₀ : Board) (hB₀ : IsInitial B₀)
    (B' : Board) (hreach : Reachable B₀ B') (hterm : IsTerminal B') :
    HasUniqueLarge B' := by
  obtain ⟨a, ha, ha1⟩ := reachable_hasLarge (initial_hasLarge hB₀) hreach
  have hne : B'.filter (fun x => 1 < x) ≠ 0 := by
    intro hz
    have hamem : a ∈ B'.filter (fun x => 1 < x) := Multiset.mem_filter.mpr ⟨ha, ha1⟩
    rw [hz] at hamem
    simp at hamem
  have hcard : 0 < (B'.filter (fun x => 1 < x)).card := Multiset.card_pos.mpr hne
  exact Nat.le_antisymm hterm (by omega)

/-- **Statement (b) — invariance of `M`.**  Any two terminal boards reachable from
the same initial board `B₀` have the same set of entries `> 1`; since (by (a)) each
has exactly one such entry, this says the terminal value `M` is the same for both. -/
theorem statement_b_invariance (B₀ : Board) (hB₀ : IsInitial B₀)
    (B₁ B₂ : Board) (h₁ : Reachable B₀ B₁) (h₂ : Reachable B₀ B₂)
    (t₁ : IsTerminal B₁) (t₂ : IsTerminal B₂) :
    ∀ M, (1 < M ∧ M ∈ B₁) ↔ (1 < M ∧ M ∈ B₂) := by
  intro M
  constructor
  · rintro ⟨hM, hmem⟩
    obtain ⟨N, hNmem, hN⟩ := reachable_hasLarge (initial_hasLarge hB₀) h₂
    have hMeq : M = Mval B₀ := terminal_value_formula B₀ hB₀ B₁ h₁ t₁ M hM hmem
    have hNeq : N = Mval B₀ := terminal_value_formula B₀ hB₀ B₂ h₂ t₂ N hN hNmem
    have hMN : M = N := hMeq.trans hNeq.symm
    exact ⟨hM, hMN.symm ▸ hNmem⟩
  · rintro ⟨hM, hmem⟩
    obtain ⟨N, hNmem, hN⟩ := reachable_hasLarge (initial_hasLarge hB₀) h₁
    have hMeq : M = Mval B₀ := terminal_value_formula B₀ hB₀ B₂ h₂ t₂ M hM hmem
    have hNeq : N = Mval B₀ := terminal_value_formula B₀ hB₀ B₁ h₁ t₁ N hN hNmem
    have hMN : M = N := hMeq.trans hNeq.symm
    exact ⟨hM, hMN.symm ▸ hNmem⟩

/-- **Value of `M` (correctness of the explicit formula).**  For any terminal board
`B'` reachable from an initial board `B₀`, the unique entry `M > 1` of `B'` equals
the invariant `Mval B₀`. -/
theorem terminal_value_eq_Mval (B₀ : Board) (hB₀ : IsInitial B₀)
    (B' : Board) (hreach : Reachable B₀ B') (hterm : IsTerminal B')
    (M : ℕ) (hM : 1 < M) (hMem : M ∈ B') :
    M = Mval B₀ := by
  exact terminal_value_formula B₀ hB₀ B' hreach hterm M hM hMem

/-- The invariant terminal value is itself `> 1`, since all initial entries exceed
`1`. -/
theorem Mval_gt_one (B₀ : Board) (hB₀ : IsInitial B₀) : 1 < Mval B₀ := by
  have hpos : PositiveBoard B₀ := initial_positive hB₀
  obtain ⟨a, ha, ha1⟩ := initial_hasLarge hB₀
  obtain ⟨p, hp, hpa⟩ := Nat.exists_prime_and_dvd (by omega : a ≠ 1)
  have hprod0 : B₀.prod ≠ 0 := ne_of_gt (Multiset.prod_pos hpos)
  have hpmem : p ∈ B₀.prod.primeFactors := Nat.mem_primeFactors.mpr
    ⟨hp, dvd_trans hpa (Multiset.dvd_prod ha), hprod0⟩
  have hexp0 : gExp p B₀ ≠ 0 :=
    (gExp_ne_zero_iff_mem_primeFactors p hp hpos).mpr hpmem
  have hfactor : 1 < p ^ gExp p B₀ := Nat.one_lt_pow hexp0 hp.one_lt
  have hMpos : 0 < Mval B₀ := by
    unfold Mval
    exact Finset.prod_pos fun q hq =>
      pow_pos (Nat.prime_of_mem_primeFactors hq).pos _
  have hdiv : p ^ gExp p B₀ ∣ Mval B₀ := by
    unfold Mval
    exact Finset.dvd_prod_of_mem (fun q => q ^ gExp q B₀) hpmem
  exact lt_of_lt_of_le hfactor (Nat.le_of_dvd hMpos hdiv)
