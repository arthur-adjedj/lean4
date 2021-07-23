/*
Copyright (c) 2018 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#pragma once
#include <functional>
#include <vector>
#include <unordered_map>
#include <lean/object.h>

namespace lean {
typedef lean_object * object_offset;

class object_compactor {
    struct max_sharing_table;
    friend struct max_sharing_hash;
    friend struct max_sharing_eq;
    std::unordered_map<object*, object_offset, std::hash<object*>, std::equal_to<object*>> m_obj_table;
    std::unique_ptr<max_sharing_table> m_max_sharing_table;
    std::vector<object*> m_todo;
    std::vector<object_offset> m_tmp;
    void * m_begin;
    void * m_end;
    void * m_capacity;
    size_t capacity() const { return static_cast<char*>(m_capacity) - static_cast<char*>(m_begin); }
    void save(object * o, object * new_o);
    void save_max_sharing(object * o, object * new_o, size_t new_o_sz);
    void * alloc(size_t sz);
    object_offset to_offset(object * o);
    void insert_terminator(object * o);
    object * copy_object(object * o);
    bool insert_constructor(object * o);
    bool insert_array(object * o);
    void insert_sarray(object * o);
    void insert_string(object * o);
    bool insert_thunk(object * o);
    bool insert_task(object * o);
    bool insert_ref(object * o);
    void insert_mpz(object * o);
public:
    object_compactor();
    object_compactor(object_compactor const &) = delete;
    object_compactor(object_compactor &&) = delete;
    ~object_compactor();
    object_compactor operator=(object_compactor const &) = delete;
    object_compactor operator=(object_compactor &&) = delete;
    void operator()(object * o);
    size_t size() const { return static_cast<char*>(m_end) - static_cast<char*>(m_begin); }
    void const * data() const { return m_begin; }
};

class compacted_region {
    void *            m_begin;
    void *            m_next;
    void *            m_end;
    void move(size_t d);
    void move(object * o);
    object * fix_object_ptr(object * o);
    void fix_constructor(object * o);
    void fix_array(object * o);
    void fix_thunk(object * o);
    void fix_ref(object * o);
    void fix_task(object * o);
    void fix_mpz(object * o);
public:
    /* Creates a compacted object region using the given region in memory.
       This object takes ownership of the region. */
    compacted_region(size_t sz, void * data);
    /* Creates a compacted object region using the object_compactor current state.
       It creates a copy of the compacted region generated by the object compactor. */
    explicit compacted_region(object_compactor const & c);
    compacted_region(compacted_region const &) = delete;
    compacted_region(compacted_region &&) = delete;
    ~compacted_region();
    compacted_region operator=(compacted_region const &) = delete;
    compacted_region operator=(compacted_region &&) = delete;
    object * read();
};
}
