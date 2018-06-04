/*
Copyright (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include "util/fresh_name.h"
#include "kernel/abstract.h"
#include "kernel/for_each_fn.h"
#include "library/metavar_util.h"
#include "library/metavar_context.h"

namespace lean {
static name *       g_meta_prefix;
static expr *       g_dummy_type;

static expr mk_meta_ref(name const & n, optional<name> const & pp_n) {
    if (pp_n)
        return mk_metavar(n, *pp_n, *g_dummy_type);
    else
        return mk_metavar(n, *g_dummy_type);
}

bool is_metavar_decl_ref(level const & u) {
    return is_meta(u) && is_prefix_of(*g_meta_prefix, meta_id(u));
}

bool is_metavar_decl_ref(expr const & e) {
    return is_metavar(e) && mlocal_type(e) == *g_dummy_type;
}

name get_metavar_decl_ref_suffix(level const & u) {
    lean_assert(is_metavar_decl_ref(u));
    return meta_id(u).replace_prefix(*g_meta_prefix, name());
}

name get_metavar_decl_ref_suffix(expr const & e) {
    lean_assert(is_metavar_decl_ref(e));
    return mlocal_name(e).replace_prefix(*g_meta_prefix, name());
}

// TODO(Leo): fix this
static name mk_meta_decl_name() {
    return mk_tagged_fresh_name(*g_meta_prefix);
}

level metavar_context::mk_univ_metavar_decl() {
    // TODO(Leo): should use name_generator
    return mk_meta_univ(mk_meta_decl_name());
}

expr metavar_context::mk_metavar_decl(optional<name> const & pp_n, local_context const & ctx, expr const & type) {
    // TODO(Leo): should use name_generator
    name n = mk_meta_decl_name();
    m_decls.insert(n, metavar_decl(ctx, head_beta_reduce(type)));
    return mk_meta_ref(n, pp_n);
}

optional<metavar_decl> metavar_context::find_metavar_decl(expr const & e) const {
    lean_assert(is_metavar_decl_ref(e));
    if (auto r = m_decls.find(mlocal_name(e)))
        return optional<metavar_decl>(*r);
    else
        return optional<metavar_decl>();
}

metavar_decl const & metavar_context::get_metavar_decl(expr const & e) const {
    if (auto r = m_decls.find(mlocal_name(e)))
        return *r;
    else
        throw exception("unknown metavariable");
}

optional<local_decl> metavar_context::find_local_decl(expr const & mvar, name const & n) const {
    auto mdecl = find_metavar_decl(mvar);
    if (!mdecl) return optional<local_decl>();
    return mdecl->get_context().find_local_decl(n);
}

local_decl metavar_context::get_local_decl(expr const & mvar, name const & n) const {
    return get_metavar_decl(mvar).get_context().get_local_decl(n);
}

expr metavar_context::get_local(expr const & mvar, name const & n) const {
    return get_local_decl(mvar, n).mk_ref();
}

void metavar_context::assign(level const & u, level const & l) {
    m_uassignment.insert(meta_id(u), l);
}

void metavar_context::assign(expr const & e, expr const & v) {
    lean_assert(!is_delayed_assigned(e));
    m_eassignment.insert(mlocal_name(e), v);
}

void metavar_context::assign(expr const & e, local_context const & lctx, list<expr> const & locals, expr const & v) {
    m_dassignment.insert(mlocal_name(e), delayed_assignment(lctx, locals, v));
}

optional<level> metavar_context::get_assignment(level const & l) const {
    lean_assert(is_metavar_decl_ref(l));
    if (auto v = m_uassignment.find(meta_id(l)))
        return some_level(*v);
    else
        return none_level();
}

optional<expr> metavar_context::get_assignment(expr const & e) const {
    lean_assert(is_metavar_decl_ref(e));
    if (auto v = m_eassignment.find(mlocal_name(e)))
        return some_expr(*v);
    else
        return none_expr();
}

optional<metavar_context::delayed_assignment> metavar_context::get_delayed_assignment(expr const & e) const {
    lean_assert(is_metavar_decl_ref(e));
    if (auto v = m_dassignment.find(mlocal_name(e)))
        return optional<delayed_assignment>(*v);
    else
        return optional<delayed_assignment>();
}

struct metavar_context::interface_impl {
    metavar_context & m_ctx;
    /* We store the set of delayed assigned variables that have been found to prevent their values
       from being visited over and over again. */
    name_set          m_delayed_found;
    interface_impl(metavar_context const & ctx):m_ctx(const_cast<metavar_context&>(ctx)) {}

    static bool is_mvar(level const & l) { return is_metavar_decl_ref(l); }
    bool is_assigned(level const & l) const { return m_ctx.is_assigned(l); }
    optional<level> get_assignment(level const & l) const { return m_ctx.get_assignment(l); }
    void assign(level const & u, level const & v) { m_ctx.assign(u, v); }

    static bool is_mvar(expr const & e) { return is_metavar_decl_ref(e); }

    optional<expr> check_delayed_assignment(expr const & e) {
        lean_assert(is_metavar_decl_ref(e));
        optional<delayed_assignment> d = m_ctx.get_delayed_assignment(e);
        if (!d)
            return none_expr();
        if (m_delayed_found.contains(mlocal_name(e)))
            return none_expr();
        /* Remark: a delayed assignment can be transformed in a regular assignment
           as soon as all metavariables occurring in the assigned value have
           been assigned. */
        expr new_v = m_ctx.instantiate_mvars(d->m_val);
        if (has_expr_metavar(new_v)) {
            m_delayed_found.insert(mlocal_name(e));
            if (!is_eqp(new_v, d->m_val))
                m_ctx.assign(e, d->m_lctx, d->m_locals, new_v);
            return none_expr();
        } else {
            m_ctx.m_dassignment.erase(mlocal_name(e));
            buffer<expr> locals;
            to_buffer(d->m_locals, locals);
            new_v = ::lean::abstract_locals(new_v, locals.size(), locals.data());
            unsigned i = locals.size();
            while (i > 0) {
                --i;
                local_decl decl = d->m_lctx.get_local_decl(locals[i]);
                expr type       = ::lean::abstract_locals(decl.get_type(), i, locals.data());
                if (optional<expr> letval = decl.get_value()) {
                    letval = ::lean::abstract_locals(*letval, i, locals.data());
                    new_v  = mk_let(decl.get_user_name(), type, *letval, new_v);
                } else {
                    new_v  = mk_lambda(decl.get_user_name(), type, new_v, decl.get_info());
                }
            }
            m_ctx.assign(e, new_v);
            return some_expr(new_v);
        }
    }

    bool is_assigned(expr const & e) const {
        lean_assert(is_metavar_decl_ref(e));
        return m_ctx.is_assigned(e) || const_cast<metavar_context::interface_impl*>(this)->check_delayed_assignment(e);
    }

    optional<expr> get_assignment(expr const & e) const {
        if (optional<expr> v = m_ctx.get_assignment(e))
            return v;
        if (optional<expr> v = const_cast<metavar_context::interface_impl*>(this)->check_delayed_assignment(e))
            return v;
        return none_expr();
    }

    void assign(expr const & m, expr const & v) { m_ctx.assign(m, v); }
    bool in_tmp_mode() const { return false; }
};


bool metavar_context::has_assigned(level const & l) const {
    return ::lean::has_assigned(interface_impl(*this), l);
}

bool metavar_context::has_assigned(expr const & e) const {
    return ::lean::has_assigned(interface_impl(*this), e);
}

level metavar_context::instantiate_mvars(level const & l) {
    interface_impl impl(*this);
    return ::lean::instantiate_mvars(impl, l);
}

expr metavar_context::instantiate_mvars(expr const & e) {
    interface_impl impl(*this);
    return ::lean::instantiate_mvars(impl, e);
}

void metavar_context::instantiate_mvars_at_type_of(expr const & m) {
    metavar_decl d = get_metavar_decl(m);
    expr type      = d.get_type();
    expr new_type  = instantiate_mvars(type);
    if (new_type != type) {
        m_decls.insert(mlocal_name(m), metavar_decl(d.get_context(), new_type));
    }
}

template<typename C>
static bool well_formed_metavar_occs(expr const & e, C const & ds, metavar_context const & ctx) {
    bool ok = true;
    for_each(e, [&](expr const & e, unsigned) {
            if (!ok) return false;
            if (!has_expr_metavar(e)) return false;
            if (is_metavar_decl_ref(e)) {
                if (auto d = ctx.find_metavar_decl(e)) {
                    if (!d->get_context().is_subset_of(ds)) {
                        /* invalid metavariable context */
                        ok = false;
                        return false;
                    }
                } else {
                    /* undefined metavariable */
                    ok = false;
                    return false;
                }
            }
            return true;
        });
    return ok;
}

bool metavar_context::well_formed(local_context const & ctx) const {
    bool ok = true;
    name_set visited;
    ctx.for_each([&](local_decl const & d) {
            if (!well_formed_metavar_occs(d.get_type(), visited, *this)) {
                ok = false;
                lean_unreachable();
            }
            if (auto v = d.get_value()) {
                if (!well_formed_metavar_occs(*v, visited, *this)) {
                    ok = false;
                    lean_unreachable();
                }
            }
            visited.insert(d.get_name());
        });
    return ok;
}

bool metavar_context::well_formed(local_context const & ctx, expr const & e) const {
    return well_formed_metavar_occs(e, ctx, *this);
}

bool well_formed(local_context const & lctx, metavar_context const & mctx) {
    if (!lctx.well_formed()) {
        lean_unreachable();
        return false;
    }
    if (!mctx.well_formed(lctx)) {
        lean_unreachable();
        return false;
    }
    return true;
}

bool well_formed(local_context const & lctx, metavar_context const & mctx, expr const & e) {
    if (!lctx.well_formed(e)) {
        lean_unreachable();
        return false;
    }
    if (!mctx.well_formed(lctx, e)) {
        lean_unreachable();
        return false;
    }
    return true;
}

void initialize_metavar_context() {
    g_meta_prefix = new name("_mlocal");
    register_name_generator_prefix(*g_meta_prefix);
    g_dummy_type  = new expr(mk_constant(name::mk_internal_unique_name()));
}

void finalize_metavar_context() {
    delete g_meta_prefix;
    delete g_dummy_type;
}
}
