module plfa.working.Naturals where

    data ℕ : Set where
      zero : ℕ
      suc : ℕ → ℕ

    seven : ℕ
    seven = suc(suc(suc(suc(suc(suc(suc(zero)))))))

    {-# BUILTIN NATURAL ℕ #-}

    import Relation.Binary.PropositionalEquality as Eq
    open Eq using (_≡_; refl)
    open Eq.≡-Reasoning using (begin_; _≡⟨⟩_; _∎)


    _+_ : ℕ → ℕ → ℕ
    zero + n = n
    (suc m) + n = suc(m + n)


    _ : 2 + 3 ≡ 5
    _ =
      begin
        2 + 3
      ≡⟨⟩
        (suc (suc zero)) + (suc (suc (suc zero)))
      ≡⟨⟩
        suc( (suc zero) + (suc (suc (suc zero))))
      ≡⟨⟩
        (suc(suc (zero + (suc (suc (suc zero))))))
      ≡⟨⟩
        (suc (suc (suc (suc (suc zero)))))
      ≡⟨⟩
        5
      ∎

    _ : 2 + 3 ≡ 5
    _ =
      begin
        2 + 3
      ≡⟨⟩
        suc (1 + 3)
      ≡⟨⟩
        suc (suc (0 + 3))
      ≡⟨⟩
        suc (suc 3)
      ≡⟨⟩
        5
      ∎

    _ : 3 + 4 ≡ 7
    _ =
      begin
        3 + 4
      ≡⟨⟩
        suc (2 + 4)
      ≡⟨⟩
        suc (2 + (suc 3))
      ≡⟨⟩
        suc (suc (2 + 3))
      ≡⟨⟩
        suc (suc  5)
      ≡⟨⟩
        7
      ∎

    _*_ : ℕ → ℕ → ℕ
    zero * n = zero
    (suc m) * n = n + (n * m)


    _ : 3 * 4 ≡ 12
    _ =
      begin
        3 * 4
      ≡⟨⟩
        (suc 2) * 4
      ≡⟨⟩
        4 + (4 * 2)
      ≡⟨⟩
        4 + ((suc 3) * 2)
      ≡⟨⟩
        4 + (2 + (2 * 3))
      ≡⟨⟩
        4 + (2 + (suc 1 * 3))
      ≡⟨⟩
        4 + (2 + (3 + (3 * 1)))
      ≡⟨⟩
        4 + (2 + (3 + (suc 2 * 1)))
      ≡⟨⟩
        4 + (2 + (3 + (1 + (1 * 2))))
      ≡⟨⟩
        12
      ∎

    _^_ : ℕ → ℕ → ℕ
    n ^ zero = suc zero
    n ^ (suc m) = n * (n ^ m)

    _ : 3 ^ 4 ≡ 81
    _ =
      begin
        3 ^ 4
      ≡⟨⟩
        3 ^ (1 + 3)
      ≡⟨⟩
        3 * (3 ^ 3)
      ≡⟨⟩
        3 * (3 * (3 ^ 2))
      ≡⟨⟩
        3 * (3 * (3 * (3 ^ 1)))
      ≡⟨⟩
        3 * (3 * (3 * 3))
      ≡⟨⟩
        81
      ∎

    _∸_ : ℕ → ℕ → ℕ
    m ∸ zero = m
    zero ∸ suc n = zero
    suc m ∸ suc n = m ∸ n

    _ : 5 ∸ 3 ≡ 2
    _ =
      begin
        5 ∸ 3
      ≡⟨⟩
        (1 + 4) ∸ (1 + 2)
      ≡⟨⟩
        4 ∸ 2
      ≡⟨⟩
        3 ∸ 1
      ≡⟨⟩
        2 ∸ 0
      ≡⟨⟩
        2
      ∎

    _ : 2 ∸ 5 ≡ 0
    _ =
      begin
        2 ∸ 5
      ≡⟨⟩
        1 ∸ 4
      ≡⟨⟩
        0 ∸ 3
      ≡⟨⟩
        0
      ∎

    data Bin : Set where
      ⟨⟩ : Bin
      _O : Bin → Bin
      _I : Bin → Bin

    inc : Bin → Bin
    inc ⟨⟩ = ⟨⟩ I
    inc (p O) = p I
    inc (p I) = (inc p) O

    _ : inc (⟨⟩ O O O O) ≡ ⟨⟩ O O O I
    _ = refl

    _ : inc (⟨⟩ O O O I) ≡ ⟨⟩ O O I O
    _ = refl

    _ : inc (⟨⟩ O O I O) ≡ ⟨⟩ O O I I
    _ = refl

    _ : inc (⟨⟩ O O I I) ≡ ⟨⟩ O I O O
    _ = refl

    _ : inc (⟨⟩ I O I I) ≡ ⟨⟩ I I O O
    _ = refl

    to : ℕ → Bin
    to zero = ⟨⟩ O
    to (suc n) = inc (to n)

    from : Bin → ℕ
    from ⟨⟩ = zero
    from (p O) = from p * 2
    from (p I) = suc ((from p) * 2)

    _ : to 3 ≡ ⟨⟩ I I
    _ = refl

    _ : from (⟨⟩ I I) ≡ 3
    _ = refl
