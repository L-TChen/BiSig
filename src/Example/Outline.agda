{-# OPTIONS --safe #-}

module Example.Outline (Id : Set) where

open import Prelude

variable
  d m m' m'' n : ℕ
  mode : Mode

-- Syntax.Simple.Term
data Ty (m : ℕ) : Set where
  `_   : Fin m → Ty m
  base : Ty m
  imp  : Ty m → Ty m → Ty m

variable
  σ σ' τ : Ty m

TSub : ℕ → ℕ → Set
TSub m m' = Vec (Ty m') m

variable
  ts Γ : TSub _ _

tsub : TSub m m' → Ty m → Ty m'
tsub ts (` i)     = V.lookup ts i
tsub ts  base     = base
tsub ts (imp t u) = imp (tsub ts t) (tsub ts u)

compTSub : TSub m' m'' → TSub m m' → TSub m m''
compTSub ts' ts = V.map (tsub ts') ts

tsub-comp : (ts : TSub m' m'') (us : TSub m m')
          → tsub (compTSub ts us) ≐ tsub ts ∘ tsub us
tsub-comp ts us (` i)     = V.lookup-map i (tsub ts) us
tsub-comp ts us  base     = refl
tsub-comp ts us (imp t u) = cong₂ imp (tsub-comp ts us t) (tsub-comp ts us u)

extTSub : (d : ℕ) → TSub m (d + m)
extTSub d = tabulate (`_ ∘ (d ↑ʳ_))

-- assuming the existence of a base type
baseTy : {m : ℕ} → Ty m
baseTy = base

fillBase : (d : ℕ) → TSub m m' → TSub (d + m) m'
fillBase _ = V.replicate baseTy V.++_

fillBase-extTSub : (d : ℕ) (ts : TSub m m')
                 → compTSub (fillBase d ts) (extTSub d) ≡ ts
fillBase-extTSub d ts =
  begin
    compTSub (fillBase d ts) (extTSub d)
      ≡⟨ refl ⟩
    V.map (tsub (fillBase d ts)) (tabulate (`_ ∘ (d ↑ʳ_)))
      ≡⟨ sym (V.tabulate-∘ (tsub (fillBase d ts)) (`_ ∘ (d ↑ʳ_))) ⟩
    tabulate (tsub (fillBase d ts) ∘ `_ ∘ (d ↑ʳ_))
      ≡⟨ refl ⟩
    tabulate (lookup (V.replicate base V.++ ts) ∘ (d ↑ʳ_))
      ≡⟨ V.tabulate-cong (V.lookup-++ʳ {m = d} (V.replicate base) ts) ⟩
    tabulate (lookup ts)
      ≡⟨ V.tabulate∘lookup ts ⟩
    ts
  ∎
  where open ≡-Reasoning

-- -- Syntax.BiTyped.RawNoMode.Term
-- data Parsed : Set where
--   `_  : Id → Parsed
--   _∋_ : Ty 0 → Parsed → Parsed
--   app : Parsed → Parsed → Parsed
--   abs : Id → Parsed → Parsed

data Raw (m : ℕ) : ℕ → Set where
  `_  : Fin n → Raw m n
  _∋_ : Ty m → Raw m n → Raw m n
  app : Raw m n → Raw m n → Raw m n
  abs : Raw m (suc n) → Raw m n

variable r s : Raw _ _

mapRaw : (Ty m → Ty m') → Raw m n → Raw m' n
mapRaw f (` i)     = ` i
mapRaw f (τ ∋ r)   = f τ ∋ mapRaw f r
mapRaw f (app r s) = app (mapRaw f r) (mapRaw f s)
mapRaw f (abs r)   = abs (mapRaw f r)

mapRaw-∘ : (f : Ty m' → Ty m'') (g : Ty m → Ty m')
           (r : Raw m n) → mapRaw (f ∘ g) r ≡ mapRaw f (mapRaw g r)
mapRaw-∘ f g (` i)     = refl
mapRaw-∘ f g (τ ∋ r)   = cong (f (g τ) ∋_) (mapRaw-∘ f g r)
mapRaw-∘ f g (app r s) = cong₂ app (mapRaw-∘ f g r) (mapRaw-∘ f g s)
mapRaw-∘ f g (abs r)   = cong  abs (mapRaw-∘ f g r)

mapRaw-cong : {f g : Ty m → Ty m'} → f ≐ g
            → (r : Raw m n) → mapRaw f r ≡ mapRaw g r
mapRaw-cong f≐g (` i)     = refl
mapRaw-cong f≐g (τ ∋  r)  = cong₂ _∋_ (f≐g τ) (mapRaw-cong f≐g r)
mapRaw-cong f≐g (app r s) = cong₂ app (mapRaw-cong f≐g r) (mapRaw-cong f≐g s)
mapRaw-cong f≐g (abs r)   = cong  abs (mapRaw-cong f≐g r)

-- module _ where

--   private variable
--     iden : Id
--     i    : Fin n
--     ids  : Vec Id n
--     p p' : Parsed

  -- data deBruijn : Parsed → ∀ {n} → Raw n → Vec Id n → Set where
  --   `_  : ids [ i ]= iden → deBruijn (` iden) (` i) ids
  --   _∋_ : σ ≡ τ → deBruijn p r ids → deBruijn (σ ∋ p) (τ ∋ r) ids
  --   app : deBruijn p r ids → deBruijn p' r' ids → deBruijn (app p p') (app r r') ids
  --   abs : deBruijn p r (iden ∷ ids) → deBruijn (abs iden p) (abs r) ids

data Typed {m : ℕ} : Ty m → {n : ℕ} → Vec (Ty m) n → Set where
  `_  : τ V.∈ Γ → Typed τ Γ
  _∋_ : (τ : Ty m) → Typed τ Γ → Typed τ Γ
  app : Typed (imp σ τ) Γ → Typed σ Γ → Typed τ Γ
  abs : Typed τ (σ ∷ Γ) → Typed (imp σ τ) Γ

eraseType : {Γ : Vec (Ty m) n} → Typed τ Γ → Raw m n
eraseType (` i)     = ` V.index i
eraseType (τ ∋ t)   = τ ∋  eraseType t
eraseType (app t u) = app (eraseType t) (eraseType u)
eraseType (abs t)   = abs (eraseType t)

data Core {m : ℕ} : Ty m → {n : ℕ} → Vec (Ty m) n → Set where
  `_  : τ V.∈ Γ → Core τ Γ
  app : Core (imp σ τ) Γ → Core σ Γ → Core τ Γ
  abs : Core τ (σ ∷ Γ) → Core (imp σ τ) Γ

toCore : Typed τ Γ → Core τ Γ
toCore (` i)     = ` i
toCore (τ ∋ t)   = toCore t
toCore (app t u) = app (toCore t) (toCore u)
toCore (abs t)   = abs (toCore t)

-- record Typed' (f : Ty m → Ty m') (τ : Ty m') (Γ : Vec (Ty m) n) (r : Raw m n) : Set where
--   constructor _,_
--   field
--     term : Typed τ (V.map f Γ)
--     proof : eraseType term ≡ mapRaw f r

-- map-∈ : ∀ {a b} {A : Set a} {B : Set b} {x n} {xs : Vec A n}
--         (f : A → B) → x V.∈ xs → f x V.∈ V.map f xs
-- map-∈ f (V.here eq) = V.here  (cong f eq)
-- map-∈ f (V.there i) = V.there (map-∈ f i)

-- index-map-∈ : ∀ {a b} {A : Set a} {B : Set b} {x n} {xs : Vec A n}
--               (f : A → B) (i : x V.∈ xs) → V.index (map-∈ f i) ≡ V.index i
-- index-map-∈ f (V.here eq) = refl
-- index-map-∈ f (V.there i) = cong suc (index-map-∈ f i)

-- module Typed'EnrichedConstructors {f : Ty m → Ty m'} where

--   var' : (i : τ V.∈ Γ) → Typed' f (f τ) Γ (` V.index i)
--   var' i = (` map-∈ f i) , cong `_ (index-map-∈ f i)

--   ann' : (τ : Ty m) → Typed' f (f τ) Γ r → Typed' f (f τ) Γ (τ ∋ r)
--   ann' τ (t , eq) = (f τ ∋ t) , cong (f τ ∋_) eq

--   app' : Typed' f (imp σ τ) Γ r → Typed' f σ Γ s → Typed' f τ Γ (app r s)
--   app' (t , teq) (u , ueq) = app t u , cong₂ app teq ueq

--   abs' : Typed' f τ (σ ∷ Γ) r → Typed' f (imp (f σ) τ) Γ (abs r)
--   abs' (t , eq) = abs t , cong abs eq

data Typed' (f : Ty m → Ty m') : Ty m' → {n : ℕ} → TSub n m → Raw m n → Set where
  `_  : (i : τ V.∈ Γ) → Typed' f (f τ) Γ (` V.index i)
  _∋_ : (τ : Ty m) → Typed' f (f τ) Γ r → Typed' f (f τ) Γ (τ ∋ r)
  app : Typed' f (imp σ τ) Γ r → Typed' f σ Γ s → Typed' f τ Γ (app r s)
  abs : Typed' f τ (σ ∷ Γ) r → Typed' f (imp (f σ) τ) Γ (abs r)

TypeInference : Set
TypeInference = {m n : ℕ} (Γ : Vec (Ty m) n) (r : Raw m n)
              → Dec (Σ[ m' ∈ ℕ ] Σ[ ts ∈ TSub m m' ] Σ[ τ ∈ Ty m' ] Typed' (tsub ts) τ Γ r)

data Raw⇆ (m : ℕ) : ℕ → Mode → Set where
  `_   : Fin n → Raw⇆ m n Inf
  _∋_  : Ty m → Raw⇆ m n Chk → Raw⇆ m n Inf
  _∋⇆_ : Ty m → Raw⇆ m n Chk → Raw⇆ m n Inf
  _↑   : Raw⇆ m n Inf → Raw⇆ m n Chk
  app  : Raw⇆ m n Inf → Raw⇆ m n Chk → Raw⇆ m n Inf
  abs  : Raw⇆ m (suc n) Chk → Raw⇆ m n Chk

variable
  r' r'' s' : Raw⇆ _ _ _

mapRaw⇆ : (Ty m → Ty m') → Raw⇆ m n mode → Raw⇆ m' n mode
mapRaw⇆ f (` i)     = ` i
mapRaw⇆ f (τ ∋  r)  = f τ ∋  mapRaw⇆ f r
mapRaw⇆ f (τ ∋⇆ r)  = f τ ∋⇆ mapRaw⇆ f r
mapRaw⇆ f (r ↑)     = mapRaw⇆ f r ↑
mapRaw⇆ f (app r s) = app (mapRaw⇆ f r) (mapRaw⇆ f s)
mapRaw⇆ f (abs r)   = abs (mapRaw⇆ f r)

data AddMeta {d m : ℕ} : {n : ℕ} → Raw m n → {mode : Mode} → Raw⇆ (d + m) n mode → Set where
  `_   : (i : Fin n) → AddMeta (` i) (` i)
  _∋_  : (τ : Ty m) → AddMeta r r' → AddMeta (τ ∋ r) (tsub (extTSub d) τ ∋ r')
  _∋⇆_ : (i : Fin (d + m)) → AddMeta r r' → AddMeta r ((` i) ∋⇆ r')
  _↑   : AddMeta r r' → AddMeta r (r' ↑)
  app  : AddMeta r r' → AddMeta s s' → AddMeta (app r s) (app r' s')
  abs  : AddMeta r r' → AddMeta (abs r) (abs r')

-- eraseMode : Raw⇆ m n mode → Maybe (Raw m n)
-- eraseMode (` i)     = ⦇ (` i) ⦈
-- eraseMode (τ ∋  r)  = ⦇ (τ ∋_) (eraseMode r) ⦈
-- eraseMode (τ ∋⇆ r)  = if isYes (isVar τ) then eraseMode r else nothing
-- eraseMode (r ↑)     =        eraseMode r
-- eraseMode (app r s) = ⦇ app (eraseMode r) (eraseMode s) ⦈
-- eraseMode (abs r)   = ⦇ abs (eraseMode r) ⦈

-- eraseMode-mapRaw⇆ : (f : Ty m → Ty m') (r : Raw⇆ m n mode)
--                   → eraseMode (mapRaw⇆ f r) ≡ mapRaw f (eraseMode r)
-- eraseMode-mapRaw⇆ f (` i)     = refl
-- eraseMode-mapRaw⇆ f (τ ∋  r)  = cong (f τ ∋_) (eraseMode-mapRaw⇆ f r)
-- eraseMode-mapRaw⇆ f (τ ∋⇆ r)  = eraseMode-mapRaw⇆ f r
-- eraseMode-mapRaw⇆ f (r ↑)     = eraseMode-mapRaw⇆ f r
-- eraseMode-mapRaw⇆ f (app r s) = cong₂ app (eraseMode-mapRaw⇆ f r) (eraseMode-mapRaw⇆ f s)
-- eraseMode-mapRaw⇆ f (abs r)   = cong  abs (eraseMode-mapRaw⇆ f r)

-- record Raw⇆' (m n : ℕ) (mode : Mode) (r : Raw m n) : Set where
--   constructor _,_
--   field
--     term : Raw⇆ m n mode
--     proof : eraseMode term ≡ just r

Bidirectionalisation : Set
Bidirectionalisation = {m n : ℕ} (r : Raw m n)
                     → Σ[ d ∈ ℕ ] Σ[ r' ∈ Raw⇆ (d + m) n Inf ] AddMeta r r'

-- ~ Syntax.BiTyped.Intrinsic.Term
data Typed⇆ {m : ℕ} : Ty m → {n : ℕ} → (Γ : Vec (Ty m) n) → Mode → Set where
  `_   : (i : τ V.∈ Γ) → Typed⇆ τ Γ Inf
  _∋_  : (τ : Ty m) → Typed⇆ τ Γ Chk → Typed⇆ τ Γ Inf
  _∋⇆_ : (τ : Ty m) → Typed⇆ τ Γ Chk → Typed⇆ τ Γ Inf
  _↑_  : Typed⇆ σ Γ Inf → σ ≡ τ → Typed⇆ τ Γ Chk
  app  : Typed⇆ (imp σ τ) Γ Inf → Typed⇆ σ Γ Chk → Typed⇆ τ Γ Inf
  abs  : Typed⇆ τ (σ ∷ Γ) Chk → Typed⇆ (imp σ τ) Γ Chk

eraseType⇆ : {Γ : Vec (Ty m) n} → Typed⇆ τ Γ mode → Raw⇆ m n mode
eraseType⇆ (` i)     = ` V.index i
eraseType⇆ (τ ∋  t)  = τ ∋  eraseType⇆ t
eraseType⇆ (τ ∋⇆ t)  = τ ∋⇆ eraseType⇆ t
eraseType⇆ (t ↑ eq)  = (eraseType⇆ t) ↑
eraseType⇆ (app t u) = app (eraseType⇆ t) (eraseType⇆ u)
eraseType⇆ (abs t)   = abs (eraseType⇆ t)

-- record Typed⇆' (f : Ty (d + m) → Ty m') (τ : Ty m') (Γ : TSub n m)
--                (r : Raw⇆ (d + m) n mode) : Set where
--   constructor _,_
--   field
--     term : Typed⇆ τ (V.map (f ∘ tsub (extTSub d)) Γ) mode
--     proof : eraseType⇆ term ≡ mapRaw⇆ f r

-- module Typed⇆'EnrichedConstructors {f : Ty (d + m) → Ty m'} {Γ : TSub n m} where

--   var' : (i : τ V.∈ Γ) → Typed⇆' f (f (tsub (extTSub d) τ)) Γ (` V.index i)
--   var' i = (` map-∈ (f ∘ tsub (extTSub d)) i) ,
--            cong `_ (index-map-∈ (f ∘ tsub (extTSub d)) i)

--   ann' : (τ : Ty (d + m)) → Typed⇆' f (f τ) Γ r' → Typed⇆' f (f τ) Γ (τ ∋ r')
--   ann' τ (t , eq) = (f τ ∋ t) , cong (f τ ∋_) eq

--   ann⇆' : (τ : Ty (d + m)) → Typed⇆' f (f τ) Γ r' → Typed⇆' f (f τ) Γ (τ ∋⇆ r')
--   ann⇆' τ (t , eq) = (f τ ∋⇆ t) , cong (f τ ∋⇆_) eq

--   emb' : Typed⇆' f σ Γ r' → σ ≡ τ → Typed⇆' f τ Γ (r' ↑)
--   emb' (t , eq) eq' = (t ↑ eq') , cong _↑ eq

--   app' : Typed⇆' f (imp σ τ) Γ r' → Typed⇆' f σ Γ s' → Typed⇆' f τ Γ (app r' s')
--   app' (t , teq) (u , ueq) = app t u , cong₂ app teq ueq

--   abs' : Typed⇆' f τ (σ ∷ Γ) r' → Typed⇆' f (imp (f (tsub (extTSub d) σ)) τ) Γ (abs r')
--   abs' (t , eq) = abs t , cong abs eq

data Typed⇆' (f : Ty (d + m) → Ty m') :
  Ty m' → {n : ℕ} → Vec (Ty m) n → {mode : Mode} → Raw⇆ (d + m) n mode → Set where
  `_   : (i : τ V.∈ Γ) → Typed⇆' f (f (tsub (extTSub d) τ)) Γ (` V.index i)
  _∋_  : (τ : Ty (d + m)) → Typed⇆' f (f τ) Γ r' → Typed⇆' f (f τ) Γ (τ ∋  r')
  _∋⇆_ : (τ : Ty (d + m)) → Typed⇆' f (f τ) Γ r' → Typed⇆' f (f τ) Γ (τ ∋⇆ r')
  _↑_  : Typed⇆' f σ Γ r' → σ ≡ τ → Typed⇆' f τ Γ (r' ↑)
  app  : Typed⇆' f (imp σ τ) Γ r' → Typed⇆' f σ Γ s' → Typed⇆' f τ Γ (app r' s')
  abs  : Typed⇆' f τ (σ ∷ Γ) r' → Typed⇆' f (imp (f (tsub (extTSub d) σ)) τ) Γ (abs r')

TypeInference⇆ : Set
TypeInference⇆ = {d m n : ℕ} (Γ : TSub n m) (r : Raw⇆ (d + m) n Inf)
               → Dec (Σ[ m' ∈ ℕ ] Σ[ ts ∈ TSub (d + m) m' ] Σ[ τ ∈ Ty m' ]
                      Typed⇆' (tsub ts) τ Γ r)

Soundness : Set
Soundness = ∀ {d m m' n τ Γ mode} {ts : TSub (d + m) m'}
              {r : Raw m n} {r' : Raw⇆ (d + m) n mode} → AddMeta r r'
            → Typed⇆' (tsub ts) τ Γ r' → Typed' (tsub ts ∘ tsub (extTSub d)) τ Γ r

Completeness : Set
Completeness = ∀ {d m m' n τ Γ mode} {ts : TSub (d + m) m'}
                 {r : Raw m n} {r' : Raw⇆ (d + m) n mode} → AddMeta r r'
               → Typed' (tsub ts ∘ tsub (extTSub d)) τ Γ r
               → Σ[ ts' ∈ TSub (d + m) m' ] Typed⇆' (tsub ts') τ Γ r'

-- module Implementation (bidir : Bidirectionalisation) (inf⇆ : TypeInference⇆)
--                       (soundness : Soundness) (completeness : Completeness) where

--   open ≡-Reasoning

--   inf : TypeInference
--   inf Γ r with bidir r
--   ... | d , r' , a = map′
--     (λ { (m' , τ , ts , t) →
--           m' , τ , compTSub ts (extTSub d) ,
--           {!   !} })
--     {!   !}
--     (inf⇆ (V.map (tsub (extTSub d)) Γ) r')

-- module Implementation (bidir : Bidirectionalisation) (inf⇆ : TypeInference⇆)
--                       (soundness : Soundness) (completeness : Completeness) where

--   open ≡-Reasoning

--   inf : TypeInference
--   inf Γ r =
--     let (d , r') = bidir r
--     in  map′
--           (λ { (m' , τ , ts , t) →
--                 m' , τ , compTSub ts (extTSub d) ,
--                 subst₂ (Typed' τ)
--                   (begin
--                      V.map (tsub ts) (V.map (tsub (extTSub d)) Γ)
--                        ≡⟨ sym (V.map-∘ (tsub ts) (tsub (extTSub d)) Γ) ⟩
--                      V.map (tsub ts ∘ tsub (extTSub d)) Γ
--                        ≡⟨ sym (V.map-cong (tsub-comp ts (extTSub d)) Γ) ⟩
--                      V.map (tsub (compTSub ts (extTSub d))) Γ
--                    ∎)
--                   (begin
--                      eraseMode (mapRaw⇆ (tsub ts) (Raw⇆'.term r'))
--                        ≡⟨ eraseMode-mapRaw⇆ (tsub ts) (Raw⇆'.term r') ⟩
--                      mapRaw (tsub ts) (eraseMode (Raw⇆'.term r'))
--                        ≡⟨ cong (mapRaw (tsub ts)) (Raw⇆'.proof r') ⟩
--                      mapRaw (tsub ts) (mapRaw (tsub (extTSub d)) r)
--                        ≡⟨ sym (mapRaw-∘ (tsub ts) (tsub (extTSub d)) r) ⟩
--                      mapRaw (tsub ts ∘ tsub (extTSub d)) r
--                        ≡⟨ sym (mapRaw-cong (tsub-comp ts (extTSub d)) r) ⟩
--                      mapRaw (tsub (compTSub ts (extTSub d))) r
--                    ∎)
--                   (soundness t) })
--           (λ { (m' , τ , ts , t) →
--                 m' , τ , fillBase d ts ,
--                 completeness
--                   (subst₂ (Typed' τ)
--                      (begin
--                         V.map (tsub ts) Γ
--                           ≡⟨ sym (V.map-cong (λ σ → cong (flip tsub σ) (fillBase-extTSub d ts)) Γ) ⟩
--                         V.map (tsub (compTSub (fillBase d ts) (extTSub d))) Γ
--                           ≡⟨ V.map-cong (tsub-comp (fillBase d ts) (extTSub d)) Γ ⟩
--                         V.map (tsub (fillBase d ts) ∘ tsub (extTSub d)) Γ
--                           ≡⟨ V.map-∘ (tsub (fillBase d ts)) (tsub (extTSub d)) Γ ⟩
--                         V.map (tsub (fillBase d ts)) (V.map (tsub (extTSub d)) Γ)
--                       ∎)
--                      (begin
--                         mapRaw (tsub ts) r
--                           ≡⟨ sym (mapRaw-cong (λ σ → cong (flip tsub σ) (fillBase-extTSub d ts)) r) ⟩
--                         mapRaw (tsub (compTSub (fillBase d ts) (extTSub d))) r
--                           ≡⟨ mapRaw-cong (tsub-comp (fillBase d ts) (extTSub d)) r ⟩
--                         mapRaw (tsub (fillBase d ts) ∘ tsub (extTSub d)) r
--                           ≡⟨ mapRaw-∘ (tsub (fillBase d ts)) (tsub (extTSub d)) r ⟩
--                         mapRaw (tsub (fillBase d ts)) (mapRaw (tsub (extTSub d)) r)
--                           ≡⟨ cong (mapRaw (tsub (fillBase d ts))) (sym (Raw⇆'.proof r')) ⟩
--                         mapRaw (tsub (fillBase d ts)) (eraseMode (Raw⇆'.term r'))
--                           ≡⟨ sym (eraseMode-mapRaw⇆ (tsub (fillBase d ts)) (Raw⇆'.term r')) ⟩
--                         eraseMode (mapRaw⇆ (tsub (fillBase d ts)) (Raw⇆'.term r'))
--                       ∎)
--                      t) })
--           (inf⇆ (V.map (tsub (extTSub d)) Γ) (Raw⇆'.term r'))

soundness : Soundness
soundness (` ._)    (` i)      = ` i
soundness (τ ∋ a)   (._ ∋ t)   = τ ∋ (soundness a t)
soundness (i ∋⇆ a)  (._ ∋⇆ t)  = soundness a t
soundness (a ↑)     (t ↑ refl) = soundness a t
soundness (app a b) (app t u)  = app (soundness a t) (soundness b u)
soundness (abs a)   (abs t)    = abs (soundness a t)

-- completeness : Completeness
-- completeness (` ._) (var i refl) = _ , var i refl
-- completeness (τ ∋  a) (ann .τ eq t) = {!   !} , ann (tsub (extTSub _) τ) {!   !} (proj₂ (completeness a t))
-- completeness (ann⇆ a eq)  t = {! completeness a t  !}
-- completeness (a ↑)     t = {!   !}
-- completeness (app a b) t = {!   !}
-- completeness (abs a)   t = {!   !}

-- map≡just : ∀ {ℓa ℓb} {A : Set ℓa} {B : Set ℓb} (f : A → B) (ma : Maybe A) {b : B}
--          → M.map f ma ≡ just b → Σ[ a ∈ A ] ma ≡ just a × f a ≡ b
-- map≡just f (just a) refl = a , refl , refl

-- module _ where

  -- open Typed'EnrichedConstructors

  -- soundness : Soundness
  -- soundness (` ._)    ((` i)      , refl) = {! var' i !}
  -- soundness (τ ∋  a)  ((._ ∋  t)  , eq  ) = {! (soundness a (t , refl)) !}
  -- soundness (i ∋⇆ a)  ((._ ∋⇆ t)  , eq  ) = {! ann' (` i) (soundness a (t , refl)) !}
  -- soundness (a ↑)     ((t ↑ refl) , eq  ) = {! soundness a (t , refl) !}
  -- soundness (app a b) (app t u    , eq  ) = {! app' (soundness a (t , refl)) (soundness b (u , refl)) !}
  -- soundness (abs a)   (abs t      , eq  ) = {! abs' (soundness a (t , refl)) !}

-- completeness : Completeness
-- completeness {r = ` i} t = {!   !}
-- completeness {r = σ ∋  r} ((τ ∋ t) , eq) = let (t' , eq') = completeness (t , {!   !})
--                                            in  (τ ∋ t') , cong₂ _∋_ {!   !} eq'
-- completeness {r = σ ∋⇆ r} (     t  , eq) = let (t' , eq') = completeness {r = r} (t , eq)
--                                            in  (_ ∋⇆ t') , {!   !}
-- completeness {r = r ↑} t = {!   !}
-- completeness {r = app r s} t = {!   !}
-- completeness {r = abs r} t = {!   !}
