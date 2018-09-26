/-
Copyright (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Avigad, Leonardo de Moura

Monad combinators, as in Haskell's Control.Monad.
-/
prelude
import init.control.monad init.control.alternative init.data.list.basic init.coe
universes u v w

def nat.mrepeat {m} [monad m] (n : nat) (f : nat → m unit) : m unit :=
n.repeat (λ i a, a *> f i) (pure ())

def list.mmap {m : Type u → Type v} [monad m] {α : Type w} {β : Type u} (f : α → m β) : list α → m (list β)
| []       := pure []
| (h :: t) := do h' ← f h, t' ← list.mmap t, pure (h' :: t')

def list.mmap' {m : Type u → Type v} [monad m] {α : Type w} {β : Type u} (f : α → m β) : list α → m punit
| []       := pure ⟨⟩
| (h :: t) := f h *> list.mmap' t

def list.mfor {m : Type u → Type v} [monad m] {α : Type w} {β : Type u} (f : α → m β) : list α → m punit :=
list.mmap' f

def mjoin {m : Type u → Type u} [monad m] {α : Type u} (a : m (m α)) : m α :=
bind a id

def list.mfilter {m : Type → Type v} [monad m] {α : Type} (f : α → m bool) : list α → m (list α)
| []       := pure []
| (h :: t) := do b ← f h, t' ← list.mfilter t, cond b (pure (h :: t')) (pure t')

def list.mfoldl {m : Type u → Type v} [monad m] {s : Type u} {α : Type w} : (s → α → m s) → s → list α → m s
| f s [] := pure s
| f s (h :: r) := do
  s' ← f s h,
  list.mfoldl f s' r

def list.mfoldr {m : Type u → Type v} [monad m] {s : Type u} {α : Type w} : (α → s → m s) → s → list α → m s
| f s [] := pure s
| f s (h :: r) := do
  s' ← list.mfoldr f s r,
  f h s'

def list.mfirst {m : Type u → Type v} [monad m] [alternative m] {α : Type w} {β : Type u} (f : α → m β) : list α → m β
| []      := failure
| (a::as) := f a <|> list.mfirst as

def list.mexists {m : Type → Type u} [monad m] {α : Type v} (f : α → m bool) : list α → m bool
| []      := pure ff
| (a::as) := do b ← f a, if b then pure tt else list.mexists as

def list.mforall {m : Type → Type u} [monad m] {α : Type v} (f : α → m bool) : list α → m bool
| []      := pure tt
| (a::as) := do b ← f a, if b then list.mforall as else pure ff

@[macro_inline] def when {m : Type → Type u} [monad m] (c : Prop) [h : decidable c] (t : m unit) : m unit :=
if c then t else pure ()

@[macro_inline] def unless {m : Type → Type u} [monad m] (c : Prop) [h : decidable c] (e : m unit) : m unit :=
if c then pure () else e

@[macro_inline] def mcond {m : Type → Type u} [monad m] {α : Type} (mbool : m bool) (tm fm : m α) : m α :=
do b ← mbool, cond b tm fm

@[macro_inline] def mwhen {m : Type → Type u} [monad m] (c : m bool) (t : m unit) : m unit :=
mcond c t (pure ())
