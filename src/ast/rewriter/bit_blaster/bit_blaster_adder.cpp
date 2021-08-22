#include "ast/rewriter/bit_blaster/bit_blaster_adder.h"

bit_blaster_adder::bit_blaster_adder(bool_rewriter & rewriter, unsigned sz, numeral const & value):
    m_rewriter(rewriter),
    m_constant(value)
{
    reduce();
    expr_ref_vector empty(m());
    m_variable.resize(sz, empty);
}

bit_blaster_adder::bit_blaster_adder(bool_rewriter & rewriter, unsigned sz, expr * const * bits):
    bit_blaster_adder(rewriter, sz)
{
    for (unsigned i = 0; i < sz; i++)
        add_bit(i, bits[i]);
}

// Compute the next height to reduce the input columns to, given the current
// maximum height, as defined by Luigi Dadda in "Some schemes for parallel
// multipliers", 1965.
//
// https://oeis.org/A061418
// https://en.wikipedia.org/wiki/Dadda_multiplier
//
// This sequence is defined here as:
//
// d(0) = 1
// d(1) = 2
// d(k) = floor(1.5 * d(k-1))
//
// The d(0) element is not in the conventional definition; it doesn't fit the
// nice recurrence relation, since floor(1.5 * 1) = 1. But including it means
// the caller doesn't need to special-case the final stage of adders.
static unsigned dadda_limit(unsigned height) {
    // Prevent overflow---though if you add up 2.8 billion bit-blasted numbers,
    // you probably run out of memory before hitting this limit.
    SASSERT(height <= UINT_MAX / 3 * 2);

    // Assuming unsigned is 32-bit, this loop can't run more than 53 times. It
    // shouldn't touch memory as long as your CPU has at least four registers.
    // So just recompute the sequence every time we need it.
    unsigned x = 1, y = 2;
    while (y < height) {
        x = y;
        // equivalent to y = y * 3 / 2 but doesn't overflow prematurely
        y += y >> 1;
    }
    return x;
}

expr_ref bit_blaster_adder::sum_bits(vector< expr_ref_vector > & columns, expr_ref_vector & out_bits) const {
    SASSERT(out_bits.empty());

    unsigned height = 0;
    for (auto & column : columns)
        if (height < column.size())
            height = column.size();

    expr_ref_vector cur(m()), next(m());
    expr_ref tmp1(m()), tmp2(m()), tmp3(m());
    expr_ref carry(m());
    carry = m().mk_false();

    while (height > 1) {
        // In each iteration, reduce the height of every column that has more
        // bits than the current Dadda limit until it has exactly the right
        // number of bits. This can add carry bits to the next column, which
        // may then need to be reduced as well.
        height = dadda_limit(height);

        SASSERT(cur.empty());
        for (auto & column : columns) {
            SASSERT(next.empty());

            // Reduce carry bits from the previous column first, followed by
            // any bits which were already in this column.
            if (cur.empty()) {
                cur.swap(column);
            } else {
                cur.append(column);
                column.reset();
            }

            if (cur.size() <= height) {
                cur.swap(column);
                continue;
            }

            unsigned excess = cur.size() - height;

            // A full adder replaces three bits with one, reducing the excess
            // by two. Do that until we don't have two excess bits left to
            // reduce. If there's one excess bit left at that point, use a half
            // adder to replace two bits with one. So the number of new bits is
            // half the excess, rounded up.
            const unsigned changed = (excess + 1) / 2;

            // To make progress, we'd better be generating some new bits.
            SASSERT(changed > 0);

            // We only replace enough bits in each round to get down to the
            // height target; the rest pass through to the next round
            // unchanged.
            const unsigned unchanged = height - changed;
            for (unsigned i = cur.size() - unchanged; i < cur.size(); i++)
                column.push_back(cur.get(i));

            unsigned i = 0;
            while (excess >= 2) {
                excess -= 2;
                expr * a = cur.get(i++);
                expr * b = cur.get(i++);
                expr * c = cur.get(i++);

                m_rewriter.mk_xor(a, b, tmp1);
                m_rewriter.mk_xor(tmp1, c, tmp2);
                column.push_back(tmp2);

                m_rewriter.mk_and(a, b, tmp2);
                m_rewriter.mk_and(tmp1, c, tmp3);
                // tmp2 and tmp3 can't be true at the same time, so use
                // whichever of mk_or vs mk_xor makes the most sense here.
                m_rewriter.mk_or(tmp2, tmp3, tmp1);
                next.push_back(tmp1);
            }

            if (excess) {
                expr * a = cur.get(i++);
                expr * b = cur.get(i++);

                m_rewriter.mk_xor(a, b, tmp1);
                column.push_back(tmp1);

                m_rewriter.mk_and(a, b, tmp1);
                next.push_back(tmp1);
            }

            SASSERT(i == cur.size() - unchanged);
            SASSERT(column.size() == height);

            cur.reset();
            next.swap(cur);
        }

        for (auto & bit : cur) {
            m_rewriter.mk_xor(carry, bit, tmp1);
            carry = tmp1;
        }
        cur.reset();
    }

    // At this point, the height of every column is 0 or 1, so generating the
    // output bits is easy.
    for (auto & column : columns)
        out_bits.push_back(column.get(0, m().mk_false()));
    SASSERT(out_bits.size() == size());

    // We return the carry separately in case the caller wants it.
    return carry;
}

expr_ref bit_blaster_adder::variable_bits(expr_ref_vector & out_bits) const {
    vector< expr_ref_vector > columns(m_variable);
    return sum_bits(columns, out_bits);
}

expr_ref bit_blaster_adder::total_bits(expr_ref_vector & out_bits) const {
    vector< expr_ref_vector > columns(m_variable);

    expr_ref one(m());
    one = m().mk_true();
    for (unsigned i = 0; i < size(); i++)
        if (m_constant.get_bit(i))
            columns[i].push_back(one);

    expr_ref carry(m());
    carry = sum_bits(columns, out_bits);
    if (m_constant.get_bit(size())) {
        m_rewriter.mk_not(carry, one);
        carry = one;
    }
    return carry;
}

bit_blaster_adder & bit_blaster_adder::add_shifted(bit_blaster_adder const & other, unsigned shift) {
    add_shifted(other.m_constant, shift);
    for (unsigned i = 0; shift + i < size(); i++)
        m_variable[shift + i].append(other.m_variable[i]);
    return *this;
}

bit_blaster_adder & bit_blaster_adder::add_shifted(unsigned sz, expr * const * bits, unsigned shift) {
    if (sz > size() - shift)
        sz = size() - shift;
    for (unsigned i = 0; i < sz; i++)
        add_bit(shift + i, bits[i]);
    return *this;
}
