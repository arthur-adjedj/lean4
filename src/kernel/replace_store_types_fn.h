/*
Copyright (c) 2013-2014 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#pragma once
#include <tuple>
#include "runtime/interrupt.h"
#include "kernel/expr.h"
#include "kernel/expr_maps.h"
#include "kernel/local_ctx.h"


namespace lean {
/**
 * TODO fix docs
   \brief Apply <tt>f</tt> to the subexpressions of a given expression.

   f is invoked for each subexpression \c s of the input expression e.
   In a call <tt>f(s, n)</tt>, n is the scope level, i.e., the number of
   bindings operators that enclosing \c s. The replaces only visits children of \c e
   if f return none_expr.
*/
expr replace_store_types(name_generator const & ngen,local_ctx const & lctx,expr const & e, std::function<optional<expr>(local_ctx const &, expr const &, buffer<expr> const &)> const & f);

}
