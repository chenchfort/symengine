#include <algorithm>
#include <exception>
#include <iterator>
#include <symengine/series_generic.h>
#include <symengine/series_visitor.h>

using SymEngine::RCP;
using SymEngine::make_rcp;

namespace SymEngine
{

RCP<const UnivariateSeries> UnivariateSeries::series(const RCP<const Basic> &t,
                                                     const std::string &x,
                                                     unsigned int prec)
{
    UnivariateExprPolynomial p({{1, Expression(1)}});
    SeriesVisitor<UnivariateExprPolynomial, Expression, UnivariateSeries>
        visitor(std::move(p), x, prec);
    return visitor.series(t);
}

std::size_t UnivariateSeries::__hash__() const
{
    std::size_t seed = UNIVARIATEPOLYNOMIAL;
    for (const auto &it : p_.dict_) {
        std::size_t temp = UNIVARIATEPOLYNOMIAL;
        hash_combine<unsigned int>(temp, it.first);
        hash_combine<Basic>(temp, *(it.second.get_basic()));
        seed += temp;
    }
    return seed + std::size_t(get_degree() * 84728863L);
}

int UnivariateSeries::compare(const Basic &other) const
{
    SYMENGINE_ASSERT(is_a<UnivariateSeries>(other))
    const UnivariateSeries &o_ = static_cast<const UnivariateSeries &>(other);
    return p_.compare(o_.get_poly());
}

RCP<const Basic> UnivariateSeries::as_basic() const
{
    return p_.get_basic(var_);
}

umap_int_basic UnivariateSeries::as_dict() const
{
    umap_int_basic map;
    for (const auto &it : p_.get_dict())
        if (it.second != 0)
            map[it.first] = it.second.get_basic();
    return map;
}

RCP<const Basic> UnivariateSeries::get_coeff(int deg) const
{
    if (p_.get_dict().count(deg) == 0)
        return zero;
    else
        return p_.get_dict().at(deg).get_basic();
}

UnivariateExprPolynomial UnivariateSeries::var(const std::string &s)
{
    return UnivariateExprPolynomial({{1, Expression(1)}});
}

Expression UnivariateSeries::convert(const Basic &x)
{
    return Expression(x.rcp_from_this());
}

int UnivariateSeries::ldegree(const UnivariateExprPolynomial &s)
{
    return s.get_dict().begin()->first;
}

class poly_t
{
public:
    std::vector<Expression> coeffs;
    signed long alloc;
    signed long length;

    poly_t() : alloc(0), length(0){};

    poly_t(signed long alloc)
    {
        if (alloc) // allocate space for alloc small coeffs
            coeffs.resize(alloc);
        else
            coeffs.clear();

        this->alloc = alloc;
        length = 0;
    }

    void normalize()
    {
        signed long i;
        for (i = length - 1; (i >= 0) && coeffs[i] == 0; i--)
            ;
        length = i + 1;
    }

    void truncate(signed long newlen)
    {
        if (length > newlen) {
            // for (signed long i = newlen; i < length; i++)
            //  coeffs.erase(coeffs.begin() + i);
            length = newlen;
            normalize();
        }
    }

    void realloc(signed long alloc)
    {
        if (alloc == 0) // Clear up, reinitialise
        {
            coeffs.clear();
            *this = poly_t();
            return;
        }

        if (this->alloc) // Realloc
        {
            truncate(alloc);
            coeffs.resize(alloc);

            if (alloc > this->alloc)
                std::fill(coeffs.begin() + this->alloc,
                          coeffs.end() - this->alloc, Expression(0));
        } else {
            coeffs.resize(alloc);
        }

        this->alloc = alloc;
    }

    void fit_length(signed long len)
    {
        if (len > alloc) {
            // At least double number of allocated coeffs
            if (len < 2 * alloc)
                len = 2 * alloc;
            realloc(len);
        }
    }

    void set_length(signed long newlen)
    {
        // if (length > newlen)
        //  for (signed long i = newlen; i < length; i++)
        //    coeffs.erase(coeffs.begin() + i);
        length = newlen;
    }

    void zero()
    {
        set_length(0);
    }

    void set_coeff(signed long n, const Expression &x)
    {
        if (x == 0) {
            if (n >= length)
                return;

            coeffs[n] = Expression(0);

            if (n == length - 1)
                normalize();
        } else {
            fit_length(n + 1);

            if (n + 1 > length) {
                for (signed long i = length; i < n; i++)
                    coeffs[i] = Expression(0);

                length = n + 1;
            }

            coeffs[n] = x;
        }
    }

    void swap(poly_t &poly2)
    {
        if (this != &poly2) {
            signed long temp;
            std::vector<Expression> temp_c;

            temp = length;
            length = poly2.length;
            poly2.length = temp;

            temp = alloc;
            alloc = poly2.alloc;
            poly2.alloc = temp;

            temp_c = coeffs;
            coeffs = poly2.coeffs;
            poly2.coeffs = temp_c;
        }
    }
};

void vec_add(Expression *res, const Expression *vec1, const Expression *vec2,
             signed long len2)
{
    for (signed long i = 0; i < len2; i++)
        res[i] = vec1[i] + vec2[i];
}

void vec_sub(Expression *res, const Expression *vec1, const Expression *vec2,
             signed long len2)
{
    for (signed long i = 0; i < len2; i++)
        res[i] = vec1[i] - vec2[i];
}

void vec_scalar_addmul_si(Expression *vec1, const Expression *vec2,
                          signed long len2, const Expression &c)
{
    int cmp = c.get_basic()->__cmp__(*Expression(0).get_basic());
    if (cmp == 0 || cmp == 1)
        for (signed long i = 0; i < len2; i++)
            vec1[i] += vec2[i] * c;
    else
        for (signed long i = 0; i < len2; i++)
            vec1[i] -= vec2[i] * c;
}

void vec_scalar_addmul(Expression *poly1, const Expression *poly2,
                       signed long len2, const Expression &x)
{
    const Expression &c = x;

    // if (!COEFF_IS_MPZ(c)) {
    if (c == 0)
        return;
    else if (c == 1)
        vec_add(poly1, poly1, poly2, len2);
    else if (c == -1)
        vec_sub(poly1, poly1, poly2, len2);
    else
        vec_scalar_addmul_si(poly1, poly2, len2, c);
    /*} else {
        signed long i;
        for (i = 0; i < len2; i++)
            *(poly1 + i) += *(poly2 + i) + Expression(*x);
        // fmpz_addmul(poly1 + i, poly2 + i, x);
    }*/
}

void vec_zero(Expression *vec, signed long len)
{
    for (signed long i = 0; i < len; i++)
        vec[i] = Expression(0);
}

void vec_set(Expression *vec1, const Expression *vec2, signed long len2)
{
    if (vec1[0] != vec2[0])
        for (signed long i = 0; i < len2; i++)
            vec1[i] = vec2[i];
}

void vec_neg(Expression *vec1, const Expression *vec2, signed long len2)
{
    for (signed long i = 0; i < len2; i++)
        vec1[i] = -vec2[i];
}

void vec_scalar_mul_si(Expression *vec1, const Expression *vec2,
                       signed long len2, const Expression &c)
{
    for (signed long i = 0; i < len2; i++)
        vec1[i] = vec2[i] * c;
}

void vec_scalar_mul(Expression *poly1, const Expression *poly2,
                    signed long len2, const Expression &x)
{
    const Expression &c = x;

    // if (!COEFF_IS_MPZ(c)) {
    if (c == 0)
        vec_zero(poly1, len2);
    else if (c == 1)
        vec_set(poly1, poly2, len2);
    else if (c == -1)
        vec_neg(poly1, poly2, len2);
    else
        vec_scalar_mul_si(poly1, poly2, len2, c);
    /*} else {
        signed long i;
        for (i = 0; i < len2; i++)
            *(poly1 + i) = *(poly2 + i) + *x;
        // fmpz_mul(poly1 + i, poly2 + i, x);
    }*/
}

void _poly_mullow_classical(Expression *res, const Expression *poly1,
                            signed long len1, const Expression *poly2,
                            signed long len2, signed long n)
{
    /* Special case if the length of output is 1 */
    if ((len1 == 1 && len2 == 1) || n == 1) {
        res[0] = poly1[0] * poly2[0];
    } else {
        /* Ordinary case */
        signed long i;

        /* Set res[i] = poly1[i]*poly2[0] */
        vec_scalar_mul(&res[0], &poly1[0], std::min(len1, n), poly2[0]);

        /* Set res[i+len1-1] = in1[len1-1]*in2[i] */
        if (n > len1)
            vec_scalar_mul(&res[len1], &poly2[1], n - len1, poly1[len1 - 1]);

        /* out[i+j] += in1[i]*in2[j] */
        for (i = 0; i < std::min(len1, n) - 1; i++)
            vec_scalar_addmul(&res[i + 1], &poly2[1], std::min(len2, n - i) - 1,
                              poly1[i]);
    }
}

void revbin1(Expression *out, const Expression *in, signed long len, signed long bits)
{
    signed long i;
    for (i = 0; i < len; i++)
        out[n_revbin(i, bits)] = in[i];
}

void revbin2(Expression *out, const Expression *in, signed long len, signed long bits)
{
    signed long i;
    for (i = 0; i < len; i++)
        out[i] = in[n_revbin(i, bits)];
}

void vec_add_rev(Expression *in1, Expression *in2, signed long bits)
{
    signed long i;
    for (i = 0; i < (1 << bits) - 1; i++) {
        signed long j = n_revbin(n_revbin(i, bits) + 1, bits);
        *(in1 + j) = *(in1 + j) + *(in2 + i);
    }
}

void _poly_mul_kara_recursive(Expression *out, Expression *rev1,
                              Expression *rev2, Expression *temp, signed long bits)
{
    signed long length = (1 << bits);
    signed long m = length / 2;

    if (length == 1) {
        *out = (*rev1) * (*rev2);
        *(out + 1) = Expression(0);
        return;
    }

    vec_add(temp, rev1, rev1 + m, m);
    vec_add(temp + m, rev2, rev2 + m, m);

    _poly_mul_kara_recursive(out, rev1, rev2, temp + 2 * m, bits - 1);

    _poly_mul_kara_recursive(out + length, temp, temp + m, temp + 2 * m,
                             bits - 1);

    _poly_mul_kara_recursive(temp, rev1 + m, rev2 + m, temp + 2 * m, bits - 1);

    vec_sub(out + length, out + length, out, length);
    vec_sub(out + length, out + length, temp, length);

    vec_add_rev(out, temp, bits);
}

void _poly_mul_karatsuba(Expression *res, const Expression *poly1, signed long len1,
                         const Expression *poly2, signed long len2)
{
    signed long length, loglen = 0;

    if (len1 == 1) {
        *res = (*poly1) * (*poly2);
        return;
    }

    while ((1 << loglen) < len1)
        loglen++;
    length = (1 << loglen);

    std::vector<Expression> rev1(4 * length);
    Expression *rev2 = &rev1[0] + length;
    Expression *out = &rev1[0] + 2 * length;
    std::vector<Expression> temp(2 * length);

    revbin1(&rev1[0], poly1, len1, loglen);
    revbin1(&rev2[0], poly2, len2, loglen);

    _poly_mul_kara_recursive(out, &rev1[0], rev2, &temp[0], loglen);

    vec_zero(res, len1 + len2 - 1);
    revbin2(res, out, len1 + len2 - 1, loglen + 1);
}

void poly_mullow_kara_recursive(Expression *out, const Expression *pol1,
                                const Expression *pol2, Expression *temp,
                                signed long len)
{
    signed long m1 = len / 2;
    signed long m2 = len - m1;
    int odd = (len & 1);

    if (len <= 6) {
        _poly_mullow_classical(out, pol1, len, pol2, len, len);
        return;
    }

    vec_add(temp + m2, pol1, pol1 + m1, m1);
    if (odd)
        *(temp + m2 + m1) = *(pol1 + 2 * m1);

    vec_add(temp + 2 * m2, pol2, pol2 + m1, m1);
    if (odd)
        *(temp + 2 * m2 + m1) = *(pol2 + 2 * m1);

    _poly_mul_karatsuba(out, pol1, m1, pol2, m1);
    *(out + 2 * m1 - 1) = Expression(0);

    poly_mullow_kara_recursive(temp, temp + m2, temp + 2 * m2, temp + 3 * m2,
                               m2);

    poly_mullow_kara_recursive(temp + m2, pol1 + m1, pol2 + m1, temp + 2 * m2,
                               m2);

    vec_sub(temp, temp, out, m2);
    vec_sub(temp, temp, temp + m2, m2);

    if (odd)
        *(out + 2 * m1) = *(temp + m2);
    vec_add(out + m1, out + m1, temp, m2);
}

/* Assumes poly1 and poly2 are not length 0. */
void _poly_mullow_karatsuba_n(Expression *res, const Expression *poly1,
                              const Expression *poly2, signed long n)
{
    signed long len, loglen = 0;

    if (n == 1) {
        *res = (*poly1) * (*poly2);
        return;
    }

    while ((1 << loglen) < n)
        loglen++;
    len = (1 << loglen);

    std::vector<Expression> temp(3 * len);

    poly_mullow_kara_recursive(res, poly1, poly2, &temp[0], n);
}

void poly_mullow_karatsuba_n(std::vector<Expression> &res, const std::vector<Expression> &poly1,
                             const std::vector<Expression> &poly2, unsigned long n)
{
    const unsigned long len1 = std::min(poly1.size(), n);
    const unsigned long len2 = std::min(poly2.size(), n);
    unsigned long i, lenr;

    std::vector<Expression> copy1, copy2;

    if (len1 == 0 || len2 == 0) {
        res[0] = Expression(0);
        return;
    }

    lenr = len1 + len2 - 1;
    if (n > lenr)
        n = lenr;

    if (len1 >= n)
        copy1 = poly1;
    else {
        copy1.resize(n);
        for (i = 0; i < len1; i++)
            copy1[i] = poly1[i];
        std::fill(copy1.begin() + len1, copy1.end() - len1, Expression(0));
    }

    if (len2 >= n)
        copy2 = poly2;
    else {
        copy2.resize(n);
        for (i = 0; i < len2; i++)
            copy2[i] = poly2[i];
        std::fill(copy2.begin() + len2, copy2.end() - len2, Expression(0));
    }

    if (&res != &poly1 && &res != &poly2) {
        res.fit_length(n);
        _poly_mullow_karatsuba_n(&res[0], &copy1[0], &copy2[0], n);
    } else {
        std::vector<Expression> t(n);
        _poly_mullow_karatsuba_n(&t[0], &copy1[0], &copy2[0], n);
        res = t;
    }
    res.set_length(n);
    res.normalize();
}

UnivariateExprPolynomial
UnivariateSeries::mul(const UnivariateExprPolynomial &a,
                      const UnivariateExprPolynomial &b, unsigned prec)
{
    std::vector<Expression> fa, fb, res;

    for (int i = 0; i < a.get_degree(); i++)
        fa[i] = a.find_cf(i);

    for (int i = 0; i < b.get_degree(); i++)
        fb[i] = b.find_cf(i);

    poly_mullow_karatsuba_n(res, fa, fb, prec);

    return UnivariateExprPolynomial(
        UnivariatePolynomial::from_vec(symbol("x"), std::move(res))
            ->get_dict());
}

UnivariateExprPolynomial
UnivariateSeries::pow(const UnivariateExprPolynomial &base, int exp,
                      unsigned prec)
{
    if (exp < 0) {
        SYMENGINE_ASSERT(base.size() == 1)
        map_int_Expr dict;
        dict[-(base.get_dict().begin()->first)]
            = 1 / base.get_dict().begin()->second;
        return pow(UnivariateExprPolynomial(dict), -exp, prec);
    }
    if (exp == 0) {
        if (base == 0 or base.get_dict().size() == 0) {
            throw std::runtime_error("Error: 0**0 is undefined.");
        } else {
            return UnivariateExprPolynomial(1);
        }
    }

    UnivariateExprPolynomial x(base);
    UnivariateExprPolynomial y(1);
    while (exp > 1) {
        if (exp % 2 == 0) {
            x = mul(x, x, prec);
            exp /= 2;
        } else {
            y = mul(x, y, prec);
            x = mul(x, x, prec);
            exp = (exp - 1) / 2;
        }
    }
    return mul(x, y, prec);
}

Expression UnivariateSeries::find_cf(const UnivariateExprPolynomial &s,
                                     const UnivariateExprPolynomial &var,
                                     int deg)
{
    if (s.get_dict().count(deg) == 0)
        return Expression(0);
    else
        return (s.get_dict()).at(deg);
}

Expression UnivariateSeries::root(Expression &c, unsigned n)
{
    return pow_ex(c, 1 / Expression(n));
}

UnivariateExprPolynomial
UnivariateSeries::diff(const UnivariateExprPolynomial &s,
                       const UnivariateExprPolynomial &var)
{
    if (var.get_dict().size() == 1 and var.get_dict().at(1) == Expression(1)) {
        map_int_Expr d;
        for (const auto &p : s.get_dict()) {
            if (p.first != 0)
                d[p.first - 1] = p.second * p.first;
        }
        return UnivariateExprPolynomial(d);
    } else {
        return UnivariateExprPolynomial({{0, Expression(0)}});
    }
}

UnivariateExprPolynomial
UnivariateSeries::integrate(const UnivariateExprPolynomial &s,
                            const UnivariateExprPolynomial &var)
{
    map_int_Expr dict;
    for (auto &it : s.get_dict()) {
        if (it.first != -1) {
            dict.insert(std::pair<int, Expression>(it.first + 1,
                                                   it.second / (it.first + 1)));
        } else {
            throw std::runtime_error("Not Implemented");
        }
    }

    return UnivariateExprPolynomial(dict);
}

UnivariateExprPolynomial
UnivariateSeries::subs(const UnivariateExprPolynomial &s,
                       const UnivariateExprPolynomial &var,
                       const UnivariateExprPolynomial &r, unsigned prec)
{
    UnivariateExprPolynomial result({{1, Expression(1)}});

    for (auto &i : s.get_dict())
        result += i.second * pow(r, i.first, prec);

    return result;
}

Expression UnivariateSeries::sin(const Expression &c)
{
    return SymEngine::sin(c.get_basic());
}

Expression UnivariateSeries::cos(const Expression &c)
{
    return SymEngine::cos(c.get_basic());
}

Expression UnivariateSeries::tan(const Expression &c)
{
    return SymEngine::tan(c.get_basic());
}

Expression UnivariateSeries::asin(const Expression &c)
{
    return SymEngine::asin(c.get_basic());
}

Expression UnivariateSeries::acos(const Expression &c)
{
    return SymEngine::acos(c.get_basic());
}

Expression UnivariateSeries::atan(const Expression &c)
{
    return SymEngine::atan(c.get_basic());
}

Expression UnivariateSeries::sinh(const Expression &c)
{
    return SymEngine::sinh(c.get_basic());
}

Expression UnivariateSeries::cosh(const Expression &c)
{
    return SymEngine::cosh(c.get_basic());
}

Expression UnivariateSeries::tanh(const Expression &c)
{
    return SymEngine::tanh(c.get_basic());
}

Expression UnivariateSeries::asinh(const Expression &c)
{
    return SymEngine::asinh(c.get_basic());
}

Expression UnivariateSeries::atanh(const Expression &c)
{
    return SymEngine::atanh(c.get_basic());
}

Expression UnivariateSeries::exp(const Expression &c)
{
    return SymEngine::exp(c.get_basic());
}

Expression UnivariateSeries::log(const Expression &c)
{
    return SymEngine::log(c.get_basic());
}

} // SymEngine
