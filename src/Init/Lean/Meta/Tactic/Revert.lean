/-
Copyright (c) 2020 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
prelude
import Init.Lean.Meta.Tactic.Util

namespace Lean
namespace Meta

def revert (mvarId : MVarId) (fvars : Array FVarId) : MetaM (Array FVarId × MVarId) :=
if fvars.isEmpty then pure (fvars, mvarId)
else withMVarContext mvarId $ do
  checkNotAssigned mvarId `revert;
  e ← elimMVarDeps (fvars.map mkFVar) (mkMVar mvarId);
  pure $ e.withApp $ fun mvar args => (args.map Expr.fvarId!, mvar.mvarId!)

end Meta
end Lean
