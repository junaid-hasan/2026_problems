import Mathlib
set_option backward.isDefEq.respectTransparency false

def IsValidSeq (a : ℕ → ℕ) : Prop :=
  (∀ n, 1 < a n) ∧
  (∀ n, a n < a (n + 1) ∧
        (∀ i ≤ n, 1 < Nat.gcd (a (n + 1)) (a i)) ∧
        (∀ b, a n < b → b < a (n + 1) → ∃ i ≤ n, Nat.gcd b (a i) = 1))

namespace P6Solution

def Good (a : ℕ → ℕ) (b : ℕ) : Prop :=
  ∀ i, 1 < Nat.gcd b (a i)

lemma valid_strictMono {a : ℕ → ℕ} (ha : IsValidSeq a) : StrictMono a := by
  exact strictMono_nat_of_lt_succ fun n => ha.2 n |>.1

lemma valid_lower_bound {a : ℕ → ℕ} (ha : IsValidSeq a) (n : ℕ) :
    a 0 + n ≤ a n := by
  induction n with
  | zero => simp
  | succ n ih =>
      have hs := ha.2 n |>.1
      omega

lemma valid_pairwise_gcd {a : ℕ → ℕ} (ha : IsValidSeq a) (i j : ℕ) :
    1 < Nat.gcd (a i) (a j) := by
  rcases lt_trichotomy i j with hij | rfl | hji
  · obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : j ≠ 0)
    simpa [Nat.gcd_comm, Nat.succ_eq_add_one] using ha.2 k |>.2.1 i (by omega)
  · simpa using ha.1 i
  · obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : i ≠ 0)
    simpa [Nat.succ_eq_add_one] using ha.2 k |>.2.1 j (by omega)

lemma good_of_mem_range {a : ℕ → ℕ} (ha : IsValidSeq a) (n : ℕ) :
    Good a (a n) := by
  intro i
  exact valid_pairwise_gcd ha n i

lemma mem_range_of_good_of_lt {a : ℕ → ℕ} (ha : IsValidSeq a) {b : ℕ}
    (hb0 : a 0 < b) (hb : Good a b) : ∃ n, a n = b := by
  have hex : ∃ n, b ≤ a n := by
    refine ⟨b, ?_⟩
    have := valid_lower_bound ha b
    omega
  have hbn : b ≤ a (Nat.find hex) := Nat.find_spec hex
  have hn0 : Nat.find hex ≠ 0 := by
    intro hn
    rw [hn] at hbn
    omega
  obtain ⟨k, hk⟩ := Nat.exists_eq_succ_of_ne_zero hn0
  rw [hk] at hbn
  have hkb : a k < b := by
    by_contra hnot
    have hle : b ≤ a k := by omega
    have hfindle : Nat.find hex ≤ k := Nat.find_min' hex hle
    omega
  have hEq : b = a (k + 1) := by
    change b ≤ a (k + 1) at hbn
    by_contra hne
    have hlt : b < a (k + 1) := by omega
    obtain ⟨i, hi, hcop⟩ := ha.2 k |>.2.2 b hkb hlt
    have hgood := hb i
    omega
  exact ⟨k + 1, hEq.symm⟩

lemma good_iff_mem_range_above {a : ℕ → ℕ} (ha : IsValidSeq a) {b : ℕ}
    (hb0 : a 0 < b) : Good a b ↔ ∃ n, a n = b := by
  constructor
  · exact mem_range_of_good_of_lt ha hb0
  · rintro ⟨n, rfl⟩
    exact good_of_mem_range ha n

lemma not_good_has_smaller_coprime_term {a : ℕ → ℕ} (ha : IsValidSeq a) {b : ℕ}
    (hb0 : a 0 < b) (hb : ¬Good a b) : ∃ i, a i < b ∧ Nat.gcd b (a i) = 1 := by
  have hex : ∃ n, b ≤ a n := by
    refine ⟨b, ?_⟩
    have := valid_lower_bound ha b
    omega
  have hbn : b ≤ a (Nat.find hex) := Nat.find_spec hex
  have hn0 : Nat.find hex ≠ 0 := by
    intro hn
    rw [hn] at hbn
    omega
  obtain ⟨k, hk⟩ := Nat.exists_eq_succ_of_ne_zero hn0
  rw [hk] at hbn
  have hkb : a k < b := by
    by_contra hnot
    have hle : b ≤ a k := by omega
    have hfindle : Nat.find hex ≤ k := Nat.find_min' hex hle
    omega
  have hlt : b < a (k + 1) := by
    change b ≤ a (k + 1) at hbn
    have hne : b ≠ a (k + 1) := by
      intro heq
      apply hb
      rw [heq]
      exact good_of_mem_range ha (k + 1)
    omega
  obtain ⟨i, hi, hcop⟩ := ha.2 k |>.2.2 b hkb hlt
  refine ⟨i, ?_, hcop⟩
  exact (valid_strictMono ha).monotone hi |>.trans_lt hkb

lemma good_pairwise {a : ℕ → ℕ} (ha : IsValidSeq a) {b c : ℕ}
    (hb1 : 1 < b) (hc1 : 1 < c) (hb : Good a b) (hc : Good a c) :
    1 < Nat.gcd b c := by
  let e := a 0 + 1
  have hbpow : a 0 < b ^ e := by
    have htwo : e < 2 ^ e := Nat.lt_two_pow_self
    have hmono : 2 ^ e ≤ b ^ e := by
      gcongr
      exact Nat.succ_le_iff.mpr hb1
    exact lt_of_lt_of_le (lt_trans (by simp [e]) htwo) hmono
  have hcpow : a 0 < c ^ e := by
    have htwo : e < 2 ^ e := Nat.lt_two_pow_self
    have hmono : 2 ^ e ≤ c ^ e := by
      gcongr
      exact Nat.succ_le_iff.mpr hc1
    exact lt_of_lt_of_le (lt_trans (by simp [e]) htwo) hmono
  have hbgood : Good a (b ^ e) := by
    intro i
    have hd : Nat.gcd b (a i) ∣ Nat.gcd (b ^ e) (a i) :=
      Nat.dvd_gcd (Nat.gcd_dvd_left b (a i) |>.trans (dvd_pow_self b (by omega)))
        (Nat.gcd_dvd_right b (a i))
    exact lt_of_lt_of_le (hb i)
      (Nat.le_of_dvd (Nat.gcd_pos_of_pos_left (a i) (pow_pos (by omega) _)) hd)
  have hcgood : Good a (c ^ e) := by
    intro i
    have hd : Nat.gcd c (a i) ∣ Nat.gcd (c ^ e) (a i) :=
      Nat.dvd_gcd (Nat.gcd_dvd_left c (a i) |>.trans (dvd_pow_self c (by omega)))
        (Nat.gcd_dvd_right c (a i))
    exact lt_of_lt_of_le (hc i)
      (Nat.le_of_dvd (Nat.gcd_pos_of_pos_left (a i) (pow_pos (by omega) _)) hd)
  obtain ⟨m, hm⟩ := mem_range_of_good_of_lt ha hbpow hbgood
  obtain ⟨n, hn⟩ := mem_range_of_good_of_lt ha hcpow hcgood
  have hp := valid_pairwise_gcd ha m n
  rw [hm, hn] at hp
  by_contra hnot
  have hEq : Nat.gcd b c = 1 := by
    have hpos : 0 < Nat.gcd b c := Nat.gcd_pos_of_pos_left c (by omega)
    omega
  have hcop : Nat.Coprime b c := hEq
  have hpows := hcop.pow e e
  rw [Nat.Coprime] at hpows
  omega

lemma valid_next_le_of_good {a : ℕ → ℕ} (ha : IsValidSeq a) (n b : ℕ)
    (hcur : a n < b) (hb : Good a b) : a (n + 1) ≤ b := by
  by_contra hnot
  have hlt : b < a (n + 1) := by omega
  obtain ⟨i, hi, hcop⟩ := ha.2 n |>.2.2 b hcur hlt
  have hg := hb i
  omega

lemma valid_gap_le_initial {a : ℕ → ℕ} (ha : IsValidSeq a) (n : ℕ) :
    a (n + 1) ≤ a n + a 0 := by
  let b := (a n / a 0 + 1) * a 0
  have ha0pos : 0 < a 0 := by have := ha.1 0; omega
  have hmod : a n % a 0 < a 0 := Nat.mod_lt _ ha0pos
  have hdecomp := Nat.mod_add_div (a n) (a 0)
  have hbform : b = a 0 * (a n / a 0) + a 0 := by
    dsimp [b]
    ring
  have hcur : a n < b := by
    rw [hbform]
    omega
  have hbound : b ≤ a n + a 0 := by
    rw [hbform]
    omega
  have hb : Good a b := by
    intro i
    have hg := valid_pairwise_gcd ha 0 i
    have hd : Nat.gcd (a 0) (a i) ∣ Nat.gcd b (a i) := by
      apply Nat.dvd_gcd
      · exact (Nat.gcd_dvd_left (a 0) (a i)).trans ⟨a n / a 0 + 1, by
          dsimp [b]
          ac_rfl⟩
      · exact Nat.gcd_dvd_right (a 0) (a i)
    exact lt_of_lt_of_le hg
      (Nat.le_of_dvd (Nat.gcd_pos_of_pos_left (a i) (by dsimp [b]; positivity)) hd)
  exact (valid_next_le_of_good ha n b hcur hb).trans hbound

def prefixProduct (a : ℕ → ℕ) (N : ℕ) : ℕ :=
  ∏ i ∈ Finset.range (N + 1), a i

lemma prefixProduct_pos {a : ℕ → ℕ} (ha : IsValidSeq a) (N : ℕ) :
    0 < prefixProduct a N := by
  unfold prefixProduct
  exact Finset.prod_pos fun i _ => by have := ha.1 i; omega

lemma dvd_prefixProduct {a : ℕ → ℕ} {N i : ℕ} (hi : i ≤ N) :
    a i ∣ prefixProduct a N := by
  unfold prefixProduct
  exact Finset.dvd_prod_of_mem a (Finset.mem_range.mpr (by omega))

lemma good_add_prefixProduct_iff {a : ℕ → ℕ} {N : ℕ}
    (hfinite : ∀ b, Good a b ↔ ∀ i ≤ N, 1 < Nat.gcd b (a i)) (b : ℕ) :
    Good a (b + prefixProduct a N) ↔ Good a b := by
  rw [hfinite, hfinite]
  constructor <;> intro h i hi
  · have hgi := h i hi
    obtain ⟨k, hk⟩ := dvd_prefixProduct (a := a) hi
    rw [hk] at hgi
    simpa [Nat.gcd_comm, Nat.gcd_add_mul_left_right] using hgi
  · obtain ⟨k, hk⟩ := dvd_prefixProduct (a := a) hi
    have hgi := h i hi
    rw [hk]
    simpa [Nat.gcd_comm, Nat.gcd_add_mul_left_right] using hgi

theorem main_of_good_period (a : ℕ → ℕ) (ha : IsValidSeq a) (L : ℕ) (hL : 0 < L)
    (hperiod : ∀ b, Good a (b + L) ↔ Good a b) :
    ∃ T L : ℕ, 0 < T ∧ 0 < L ∧ ∀ n, a (n + T) = a n + L := by
  have hGood0 : Good a (a 0) := good_of_mem_range ha 0
  have hGoodShift : Good a (a 0 + L) := (hperiod (a 0)).mpr hGood0
  obtain ⟨T, hT⟩ := mem_range_of_good_of_lt ha (by omega) hGoodShift
  have hTpos : 0 < T := by
    by_contra hzero
    have : T = 0 := by omega
    subst T
    simp at hT
    omega
  refine ⟨T, L, hTpos, hL, ?_⟩
  intro n
  induction n with
  | zero => simpa using hT
  | succ n ih =>
      have hCandGood : Good a (a (n + 1) + L) :=
        (hperiod (a (n + 1))).mpr (good_of_mem_range ha (n + 1))
      have hcur : a (n + T) < a (n + 1) + L := by
        rw [ih]
        have hs := ha.2 n |>.1
        omega
      have hupper0 := valid_next_le_of_good ha (n + T) (a (n + 1) + L) hcur hCandGood
      have hupper : a (n + 1 + T) ≤ a (n + 1) + L := by
        simpa only [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hupper0
      have hlower : a (n + 1) + L ≤ a (n + 1 + T) := by
        by_contra hnot
        have hlt : a (n + 1 + T) < a (n + 1) + L := by omega
        have hindex : n + T < n + 1 + T := by omega
        have hstep := valid_strictMono ha hindex
        have hshift : a n + L < a (n + 1 + T) := by
          rw [ih] at hstep
          exact hstep
        have hLle : L ≤ a (n + 1 + T) := by omega
        let d := a (n + 1 + T) - L
        have hdrepr : d + L = a (n + 1 + T) := by
          dsimp [d]
          omega
        have hdgood : Good a d := by
          apply (hperiod d).mp
          rw [hdrepr]
          exact good_of_mem_range ha (n + 1 + T)
        have hnd : a n < d := by
          dsimp [d]
          omega
        have hnext := valid_next_le_of_good ha n d hnd hdgood
        dsimp [d] at hnext
        omega
      exact Nat.le_antisymm hupper hlower

theorem main_of_finite_prefix (a : ℕ → ℕ) (ha : IsValidSeq a)
    (hprefix : ∃ N, ∀ b, Good a b ↔ ∀ i ≤ N, 1 < Nat.gcd b (a i)) :
    ∃ T L : ℕ, 0 < T ∧ 0 < L ∧ ∀ n, a (n + T) = a n + L := by
  obtain ⟨N, hfinite⟩ := hprefix
  let L := prefixProduct a N
  apply main_of_good_period a ha L (prefixProduct_pos ha N)
  intro b
  exact good_add_prefixProduct_iff hfinite b

def radical (n : ℕ) : ℕ :=
  ∏ p ∈ n.primeFactors, p

lemma radical_dvd (n : ℕ) : radical n ∣ n := by
  exact Nat.prod_primeFactors_dvd n

lemma radical_squarefree (n : ℕ) : Squarefree (radical n) := by
  unfold radical
  apply Finset.squarefree_prod_of_pairwise_isCoprime
  · intro p hp q hq hpq
    exact Nat.coprime_iff_isRelPrime.mp
      ((Nat.coprime_primes (Nat.prime_of_mem_primeFactors hp)
        (Nat.prime_of_mem_primeFactors hq)).mpr hpq)
  · intro p hp
    exact (Nat.prime_of_mem_primeFactors hp).squarefree

lemma radical_pos (n : ℕ) : 0 < radical n := by
  unfold radical
  exact Finset.prod_pos fun p hp => (Nat.prime_of_mem_primeFactors hp).pos

lemma good_radical {a : ℕ → ℕ} {n : ℕ} (hn1 : 1 < n) (hn : Good a n) :
    Good a (radical n) := by
  intro i
  have hg := hn i
  obtain ⟨p, hp, hpd⟩ := Nat.exists_prime_and_dvd (Nat.ne_of_gt hg)
  have hpn : p ∣ n := hpd.trans (Nat.gcd_dvd_left n (a i))
  have hpa : p ∣ a i := hpd.trans (Nat.gcd_dvd_right n (a i))
  have hmem : p ∈ n.primeFactors := hp.mem_primeFactors hpn (by omega)
  have hpr : p ∣ radical n := by
    unfold radical
    exact Finset.dvd_prod_of_mem (fun p => p) hmem
  have hd : p ∣ Nat.gcd (radical n) (a i) := Nat.dvd_gcd hpr hpa
  exact lt_of_lt_of_le hp.one_lt
    (Nat.le_of_dvd (Nat.gcd_pos_of_pos_left (a i) (radical_pos n)) hd)

lemma not_good_one {a : ℕ → ℕ} : ¬Good a 1 := by
  intro h
  have := h 0
  simp at this

lemma good_zero {a : ℕ → ℕ} (ha : IsValidSeq a) : Good a 0 := by
  intro i
  simpa using ha.1 i

lemma coprime_term_of_not_good {a : ℕ → ℕ} (ha : IsValidSeq a) {d : ℕ}
    (hd : ¬Good a d) : ∃ i, Nat.gcd d (a i) = 1 := by
  simp only [Good, not_forall] at hd
  obtain ⟨i, hi⟩ := hd
  refine ⟨i, ?_⟩
  have hpos : 0 < Nat.gcd d (a i) :=
    Nat.gcd_pos_of_pos_right d (by have := ha.1 i; omega)
  omega

lemma finite_coprime_witness_bound {a : ℕ → ℕ} (ha : IsValidSeq a) (N : ℕ) :
    ∃ C, ∀ d ≤ N, ¬Good a d →
      ∃ i, a i ≤ C ∧ Nat.gcd d (a i) = 1 := by
  induction N with
  | zero =>
      refine ⟨0, ?_⟩
      intro d hd hnot
      have : d = 0 := by omega
      subst d
      exact (hnot (good_zero ha)).elim
  | succ N ih =>
      obtain ⟨C, hC⟩ := ih
      by_cases hlast : Good a (N + 1)
      · refine ⟨C, ?_⟩
        intro d hd hnot
        by_cases heq : d = N + 1
        · subst d
          exact (hnot hlast).elim
        · exact hC d (by omega) hnot
      · obtain ⟨i, hi⟩ := coprime_term_of_not_good ha hlast
        refine ⟨max C (a i), ?_⟩
        intro d hd hnot
        by_cases heq : d = N + 1
        · subst d
          exact ⟨i, Nat.le_max_right _ _, hi⟩
        · obtain ⟨j, hjC, hj⟩ := hC d (by omega) hnot
          exact ⟨j, hjC.trans (Nat.le_max_left _ _), hj⟩

lemma exists_minimal_good_divisor {a : ℕ → ℕ} {x : ℕ}
    (hx1 : 1 < x) (hx : Good a x) :
    ∃ m, 1 < m ∧ Squarefree m ∧ m ∣ x ∧ Good a m ∧
      ∀ d, 1 < d → Squarefree d → d ∣ m → d < m → ¬Good a d := by
  classical
  let P : ℕ → Prop := fun m => 1 < m ∧ Squarefree m ∧ m ∣ x ∧ Good a m
  have hradGood : Good a (radical x) := good_radical hx1 hx
  have hrad1 : 1 < radical x := by
    have hp := radical_pos x
    have hn : radical x ≠ 1 := by
      intro heq
      apply not_good_one (a := a)
      simpa [heq] using hradGood
    omega
  have hex : ∃ m, P m := ⟨radical x, hrad1, radical_squarefree x,
    radical_dvd x, hradGood⟩
  let m := Nat.find hex
  have hm : P m := Nat.find_spec hex
  refine ⟨m, hm.1, hm.2.1, hm.2.2.1, hm.2.2.2, ?_⟩
  intro d hd1 hds hdm hlt hdgood
  have hdprop : P d := ⟨hd1, hds, hdm.trans hm.2.2.1, hdgood⟩
  have hle : m ≤ d := Nat.find_min' hex hdprop
  omega

lemma prime_dvd_of_good_coprime_cofactor {a : ℕ → ℕ} (ha : IsValidSeq a)
    {m d p x : ℕ} (hp : p.Prime) (hm : m = d * p)
    (hcop : Nat.gcd d x = 1) (hm1 : 1 < m) (hx1 : 1 < x)
    (hmgood : Good a m) (hxgood : Good a x) : p ∣ x := by
  have hpair := good_pairwise ha hm1 hx1 hmgood hxgood
  obtain ⟨q, hq, hqg⟩ := Nat.exists_prime_and_dvd (Nat.ne_of_gt hpair)
  have hqm : q ∣ m := hqg.trans (Nat.gcd_dvd_left m x)
  have hqx : q ∣ x := hqg.trans (Nat.gcd_dvd_right m x)
  rw [hm] at hqm
  rcases hq.dvd_mul.mp hqm with hqd | hqp
  · have hqone : q ∣ 1 := by
      rw [← hcop]
      exact Nat.dvd_gcd hqd hqx
    have : q ≤ 1 := Nat.le_of_dvd (by decide) hqone
    exact (not_lt_of_ge this hq.one_lt).elim
  · have heq : q = p := (Nat.prime_dvd_prime_iff_eq hq hp).mp hqp
    simpa [heq] using hqx

lemma minimal_good_prime_le_bound {a : ℕ → ℕ} (ha : IsValidSeq a) {C : ℕ}
    (hC : ∀ d ≤ a 0, ¬Good a d →
      ∃ i, a i ≤ C ∧ Nat.gcd d (a i) = 1) :
    ∀ m, 1 < m → Squarefree m → Good a m →
      (∀ d, 1 < d → Squarefree d → d ∣ m → d < m → ¬Good a d) →
      ∀ p, p.Prime → p ∣ m → p ≤ C := by
  intro m
  induction m using Nat.strong_induction_on with
  | h m ih =>
      intro hm1 hmsq hmgood hmin p hp hpm
      let d := m / p
      have hmpos : 0 < m := by omega
      have hp_le : p ≤ m := Nat.le_of_dvd hmpos hpm
      have hdpos : 0 < d := by
        dsimp [d]
        exact Nat.div_pos hp_le hp.pos
      have hmfac : m = d * p := by
        dsimp [d]
        exact (Nat.div_mul_cancel hpm).symm
      have hdvd : d ∣ m := by
        dsimp [d]
        exact Nat.div_dvd_of_dvd hpm
      have hdlt : d < m := by
        dsimp [d]
        exact Nat.div_lt_self hmpos hp.one_lt
      have hdsq : Squarefree d := hmsq.squarefree_of_dvd hdvd
      have hdnot : ¬Good a d := by
        intro hdgood
        have hdne : d ≠ 1 := by
          intro heq
          apply not_good_one (a := a)
          simpa [heq] using hdgood
        have hd1 : 1 < d := by omega
        exact hmin d hd1 hdsq hdvd hdlt hdgood
      by_cases hdsmall : d ≤ a 0
      · obtain ⟨i, haiC, hcop⟩ := hC d hdsmall hdnot
        have hpai : p ∣ a i := prime_dvd_of_good_coprime_cofactor ha hp hmfac hcop
          hm1 (ha.1 i) hmgood (good_of_mem_range ha i)
        exact (Nat.le_of_dvd (by have := ha.1 i; omega) hpai).trans haiC
      · have ha0d : a 0 < d := by omega
        obtain ⟨i, haid, hcop⟩ := not_good_has_smaller_coprime_term ha ha0d hdnot
        obtain ⟨m', hm'1, hm'sq, hm'dvd, hm'good, hm'min⟩ :=
          exists_minimal_good_divisor (ha.1 i) (good_of_mem_range ha i)
        have hm'le : m' ≤ a i := Nat.le_of_dvd (by have := ha.1 i; omega) hm'dvd
        have hm'lt : m' < m := by omega
        have hcop' : Nat.gcd d m' = 1 := by
          exact (show Nat.Coprime d (a i) from hcop).of_dvd_right hm'dvd
        have hpm' : p ∣ m' := prime_dvd_of_good_coprime_cofactor ha hp hmfac hcop'
          hm1 hm'1 hmgood hm'good
        exact ih m' hm'lt hm'1 hm'sq hm'good hm'min p hp hpm'

lemma squarefree_dvd_primorial_of_prime_le {m C : ℕ} (hmsq : Squarefree m)
    (hprime : ∀ p, p.Prime → p ∣ m → p ≤ C) : m ∣ primorial C := by
  have hsub : m.primeFactors ⊆ (Finset.range (C + 1)).filter Nat.Prime := by
    intro p hp
    have hpp : p.Prime := Nat.prime_of_mem_primeFactors hp
    have hpd : p ∣ m := Nat.dvd_of_mem_primeFactors hp
    have hpC := hprime p hpp hpd
    simp only [Finset.mem_filter, Finset.mem_range]
    exact ⟨by omega, hpp⟩
  have hprod := Finset.prod_dvd_prod_of_subset m.primeFactors
    ((Finset.range (C + 1)).filter Nat.Prime) (fun p => p) hsub
  rw [Nat.prod_primeFactors_of_squarefree hmsq] at hprod
  exact hprod

lemma good_of_dvd {a : ℕ → ℕ} (ha : IsValidSeq a) {d b : ℕ}
    (hd : Good a d) (hdb : d ∣ b) : Good a b := by
  intro i
  have hg := hd i
  have hdiv : Nat.gcd d (a i) ∣ Nat.gcd b (a i) :=
    Nat.dvd_gcd ((Nat.gcd_dvd_left d (a i)).trans hdb) (Nat.gcd_dvd_right d (a i))
  exact lt_of_lt_of_le hg
    (Nat.le_of_dvd (Nat.gcd_pos_of_pos_right b (by have := ha.1 i; omega)) hdiv)

lemma exists_good_core_divisor {a : ℕ → ℕ} (ha : IsValidSeq a) {C x : ℕ}
    (hC : ∀ d ≤ a 0, ¬Good a d →
      ∃ i, a i ≤ C ∧ Nat.gcd d (a i) = 1)
    (hx1 : 1 < x) (hx : Good a x) :
    ∃ m, 1 < m ∧ Good a m ∧ m ∣ x ∧ m ∣ primorial C := by
  obtain ⟨m, hm1, hmsq, hmx, hmgood, hmin⟩ := exists_minimal_good_divisor hx1 hx
  have hpbound : ∀ p, p.Prime → p ∣ m → p ≤ C :=
    minimal_good_prime_le_bound ha hC m hm1 hmsq hmgood hmin
  exact ⟨m, hm1, hmgood, hmx, squarefree_dvd_primorial_of_prime_le hmsq hpbound⟩

theorem main_of_coprime_witness_bound (a : ℕ → ℕ) (ha : IsValidSeq a) (C : ℕ)
    (hC : ∀ d ≤ a 0, ¬Good a d →
      ∃ i, a i ≤ C ∧ Nat.gcd d (a i) = 1) :
    ∃ T L : ℕ, 0 < T ∧ 0 < L ∧ ∀ n, a (n + T) = a n + L := by
  let L := primorial C
  have hLpos : 0 < L := by
    dsimp [L]
    exact primorial_pos C
  obtain ⟨m0, hm01, hm0good, hm0dvd, hm0L⟩ :=
    exists_good_core_divisor ha hC (ha.1 0) (good_of_mem_range ha 0)
  have hLgood : Good a L := by
    apply good_of_dvd ha hm0good
    exact hm0L
  apply main_of_good_period a ha L hLpos
  intro b
  constructor
  · intro hshift
    by_cases hb0 : b = 0
    · subst b
      exact good_zero ha
    · have hsum1 : 1 < b + L := by
        have hbpos : 0 < b := Nat.pos_of_ne_zero hb0
        omega
      obtain ⟨m, hm1, hmgood, hmsum, hmL⟩ :=
        exists_good_core_divisor ha hC hsum1 hshift
      apply good_of_dvd ha hmgood
      exact (Nat.dvd_add_iff_left hmL).mpr hmsum
  · intro hb
    by_cases hb0 : b = 0
    · subst b
      simpa using hLgood
    · have hb1 : 1 < b := by
        have hbpos : 0 < b := Nat.pos_of_ne_zero hb0
        have hbne1 : b ≠ 1 := by
          intro heq
          apply not_good_one (a := a)
          simpa [heq] using hb
        omega
      obtain ⟨m, hm1, hmgood, hmb, hmL⟩ :=
        exists_good_core_divisor ha hC hb1 hb
      apply good_of_dvd ha hmgood
      exact (Nat.dvd_add_iff_left hmL).mp hmb

theorem solved_main (a : ℕ → ℕ) (ha : IsValidSeq a) :
    ∃ T L : ℕ, 0 < T ∧ 0 < L ∧ ∀ n, a (n + T) = a n + L := by
  obtain ⟨C, hC⟩ := finite_coprime_witness_bound ha (a 0)
  exact main_of_coprime_witness_bound a ha C hC

end P6Solution

theorem main_theorem (a : ℕ → ℕ) (ha : IsValidSeq a) :
    ∃ T L : ℕ, 0 < T ∧ 0 < L ∧ ∀ n, a (n + T) = a n + L := by
  exact P6Solution.solved_main a ha
