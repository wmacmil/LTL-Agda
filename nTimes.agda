  -- could be nTimes tailPath
  nTimes : {A : Set} → ℕ → (A → A) → (A → A)
  nTimes zero f = id
  nTimes (suc n) f = f ∘′ nTimes n f

  -- this should be provable by basic equality arguemnts
  nTimes-homo : {A : Set} → ∀ n m f → (nTimes {A} n f) ∘  (nTimes m f) ≡ nTimes (n +' m) f
  -- nTimes-homo : {A : Set} → ∀ n m f → nTimes {A} n (nTimes m f) ≡ nTimes (n +' m) f
  nTimes-homo zero m f = refl
  nTimes-homo (suc n) m f = {!!}

  nTimes' : {A : Set} → ℕ → (A → A) → (A → A)
  -- nTimes' zero f a = a
  -- nTimes' (suc n) f a = nTimes' n f (f a)
  nTimes' zero f = id
  nTimes' (suc n) f a = nTimes' n f (f a)

  postulate
    funext : {A B : Set} → {f g : A → B} → ((a : A) → f a ≡ g a) → f ≡ g

  -- no easy way to do this?
  lemma-nTimes' : {A : Set} → ∀ f n → (a : A) → f (nTimes' n f a) ≡ nTimes' n f (f a)
  lemma-nTimes' f zero a = refl
  lemma-nTimes' f (suc n) a =
    let rec = lemma-nTimes' f n a in
    {!!}

  -- can use lemma-nTimes' and some basic equality arguements
  ntimesEqual : {A : Set} → ∀ n f → (a : A) → (nTimes n f a) ≡ nTimes' n f a
  -- ntimesEqual : {A : Set} →  ∀ n f → (nTimes {A} n f ) ≡ nTimes' n f
  ntimesEqual zero f a = refl
  ntimesEqual (suc n) f a =
    let rec = ntimesEqual n f a in
    {!rec!} -- funext (λ a → {!!})

  path-i' : ℕ → Path → Path
  path-i' zero p = p
  path-i' (suc i) p = tailPath (path-i i (p))

  -- -- tailPathCommute : ∀ m p → (tailPath (path-i m p)) ≡ path-i m (tailPath p)
  -- tailPathCommute : ∀ m p → path-i m p ≡ path-i' m p
  -- tailPathCommute zero p = refl
  -- tailPathCommute (suc m) record { infSeq = infSeq ; isTransitional = isTransitional } = {!!}

  -- tailPathCommute : ∀ m p → (tailPath (path-i m p)) ≡ path-i m (tailPath p)
  -- tailPathCommute zero p    = refl
  -- tailPathCommute (suc m) p = {!!}

  tail-lemma : ∀ n m p → (path-i n (path-i m p)) ≡ path-i (n +' m) p
  tail-lemma zero    m p    = refl
  tail-lemma (suc n) m p =
    let rec = tail-lemma n m p in
    {!!}

