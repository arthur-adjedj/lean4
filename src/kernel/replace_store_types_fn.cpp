/*
Copyright (c) 2013-2014 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include <vector>
#include <memory>
#include "kernel/replace_store_types_fn.h"

namespace lean {
class replace_rec_store_types_fn {
    name_generator             m_ngen;
    local_ctx                  m_lctx;
    std::function<optional<expr>(local_ctx const &, expr const &, buffer<expr> &)> m_f;
    // TODO, this shouldn't work, test a lot ??
    expr apply( expr const & e, buffer<expr> & fvar_types) {
        check_system("replace");

        if (optional<expr> r = m_f(m_lctx, e, fvar_types)) {
            return *r;
        } else {
            switch (e.kind()) {
            case expr_kind::Const: case expr_kind::Sort:
            case expr_kind::BVar:  case expr_kind::Lit:
            case expr_kind::MVar:  case expr_kind::FVar:
                return e;
            case expr_kind::MData: {
                expr new_e = apply(mdata_expr(e), fvar_types);
                return update_mdata(e, new_e);
            }
            case expr_kind::Proj: {
                expr new_e = apply(proj_expr(e), fvar_types);
                return update_proj(e, new_e);
            }
            case expr_kind::App: {
                expr new_f = apply(app_fn(e), fvar_types);
                expr new_a = apply(app_arg(e), fvar_types);
                return update_app(e, new_f, new_a);
            }
            case expr_kind::Pi: case expr_kind::Lambda: {
                flet<local_ctx> save_lctx(m_lctx, m_lctx);
                expr new_d = apply(binding_domain(e), fvar_types);
                expr fvar = m_lctx.mk_local_decl(m_ngen, binding_name(e), new_d, binding_info(e));
                fvar_types.push_back(fvar);
                expr new_b = apply(binding_body(e), fvar_types);
                return update_binding(e, new_d, new_b);
            }
            case expr_kind::Let: {
                flet<local_ctx> save_lctx(m_lctx, m_lctx);
                expr new_t = apply(let_type(e), fvar_types);
                expr new_v = apply(let_value(e), fvar_types);
                expr fvar = m_lctx.mk_local_decl(m_ngen, binding_name(e), new_t, new_v);
                fvar_types.push_back(fvar);
                expr new_b = apply(let_body(e), fvar_types); 
                return update_let(e, new_t, new_v, new_b);
            }
            }
            lean_unreachable();
        }
    }
public:
    template<typename F>
    replace_rec_store_types_fn(name_generator const & ngen,local_ctx const & lctx, F const & f):m_ngen(ngen), m_lctx(lctx),m_f(f) {}

    expr operator()(expr const & e) { 
        buffer<expr> buf;
        return apply(e, buf); }
};

expr replace_store_types(name_generator const & ngen, local_ctx const & lctx, expr const & e, std::function<optional<expr>(local_ctx const &, expr const &, buffer<expr> const &)> const & f) {
    return replace_rec_store_types_fn(ngen,lctx,f)(e);
}
}
