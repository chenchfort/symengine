#include <algorithm>
#include <exception>
#include <flint/fmpz_polyxx.h>
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
    UnivariateExprPolynomial p(UnivariatePolynomial::create(symbol(x), {0, 1}));
    SeriesVisitor<UnivariateExprPolynomial, Expression, UnivariateSeries>
        visitor(std::move(p), x, prec);
    return visitor.series(t);
}

std::size_t UnivariateSeries::__hash__() const
{
    return p_.get_univariate_poly()->hash()
           + std::size_t(get_degree() * 84728863L);
}

int UnivariateSeries::compare(const Basic &other) const
{
    SYMENGINE_ASSERT(is_a<UnivariateSeries>(other))
    const UnivariateSeries &o = static_cast<const UnivariateSeries &>(other);
    return p_.get_basic()->__cmp__(*o.p_.get_basic());
}

RCP<const Basic> UnivariateSeries::as_basic() const
{
    return p_.get_basic();
}

umap_int_basic UnivariateSeries::as_dict() const
{
    umap_int_basic map;
    for (const auto &it : p_.get_univariate_poly()->get_dict())
        if (it.second != 0)
            map[it.first] = it.second.get_basic();
    return map;
}

RCP<const Basic> UnivariateSeries::get_coeff(int deg) const
{
    if (p_.get_univariate_poly()->get_dict().count(deg) == 0)
        return zero;
    else
        return p_.get_univariate_poly()->get_dict().at(deg).get_basic();
}

UnivariateExprPolynomial UnivariateSeries::var(const std::string &s)
{
    return UnivariateExprPolynomial(
        UnivariatePolynomial::create(symbol(s), {0, 1}));
}

Expression UnivariateSeries::convert(const Basic &x)
{
    return Expression(x.rcp_from_this());
}

int UnivariateSeries::ldegree(const UnivariateExprPolynomial &s)
{
    return s.get_univariate_poly()->get_dict().begin()->first;
}

void fp_init2(fmpz_poly_t poly, slong alloc)
{
    if (alloc) /* allocate space for alloc small coeffs */
        poly->coeffs = (fmpz *)flint_calloc(alloc, sizeof(fmpz));
    else
        poly->coeffs = NULL;

    poly->alloc = alloc;
    poly->length = 0;
}

// FMPZ_POLY_INLINE
void _fp_set_length(fmpz_poly_t poly, slong newlen)
{
    if (poly->length > newlen) {
        slong i;
        for (i = newlen; i < poly->length; i++)
            _fmpz_demote(poly->coeffs + i);
    }
    poly->length = newlen;
}

// FMPZ_POLY_INLINE
void fp_zero(fmpz_poly_t poly)
{
    _fp_set_length(poly, 0);
}

void mullow(fmpz_poly_t res, const fmpz_poly_t poly1, const fmpz_poly_t poly2,
            slong n)
{
    const slong len1 = poly1->length;
    const slong len2 = poly2->length;

    if (len1 == 0 || len2 == 0 || n == 0) {
        fp_zero(res);
        // fmpz_poly_zero(res);
        return;
    }

    if (res == poly1 || res == poly2) {
        fmpz_poly_t t;
        fp_init2(t, n);
        mullow(t, poly1, poly2, n);
        fmpz_poly_swap(res, t);
        fmpz_poly_clear(t);
        return;
    }

    // n = FLINT_MIN(n, len1 + len2 - 1);
    n = std::min(n, len1 + len2 - 1);

    fmpz_poly_fit_length(res, n);
    if (len1 >= len2)
        _fmpz_poly_mullow(res->coeffs, poly1->coeffs, len1, poly2->coeffs, len2,
                          n);
    else
        _fmpz_poly_mullow(res->coeffs, poly2->coeffs, len2, poly1->coeffs, len1,
                          n);
    _fp_set_length(res, n);
    _fmpz_poly_normalise(res);
}

UnivariateExprPolynomial
UnivariateSeries::mul(const UnivariateExprPolynomial &a,
                      const UnivariateExprPolynomial &b, unsigned prec)
{
    map_int_Expr p;
    fmpz_poly_t fa, fb, res;
    fmpz_poly_init(fa);
    fmpz_poly_init(fb);
    fmpz_poly_init(res);
    for (const auto &it : a.get_univariate_poly()->get_dict()) {
        fmpz_t r;
        RCP<const Integer> x
            = rcp_dynamic_cast<const Integer>(it.second.get_basic());
        fmpz_set_mpz(r, get_mpz_t(x->as_int()));
        fmpz_poly_set_coeff_si(fa, it.first, fmpz_get_si(r));
    }
    for (const auto &it : b.get_univariate_poly()->get_dict()) {
        fmpz_t r;
        RCP<const Integer> x
            = rcp_dynamic_cast<const Integer>(it.second.get_basic());
        fmpz_set_mpz(r, get_mpz_t(x->as_int()));
        fmpz_poly_set_coeff_si(fb, it.first, fmpz_get_si(r));
    }
    // fmpz_poly_mullow(res, fa, fb, prec);
    mullow(res, fa, fb, prec);
    for (int i = 0; i < res->length; i++)
        p[i] = Expression(fmpz_poly_get_coeff_si(res, i));

    if (a.get_univariate_poly()->get_var()->get_name() == "")
        return UnivariateExprPolynomial(UnivariatePolynomial::from_dict(
            b.get_univariate_poly()->get_var(), std::move(p)));
    else
        return UnivariateExprPolynomial(UnivariatePolynomial::from_dict(
            a.get_univariate_poly()->get_var(), std::move(p)));
}

UnivariateExprPolynomial
UnivariateSeries::pow(const UnivariateExprPolynomial &base, int exp,
                      unsigned prec)
{
    if (exp < 0) {
        SYMENGINE_ASSERT(base.get_univariate_poly()->get_dict().size() == 1)
        map_int_Expr dict;
        dict[-(base.get_univariate_poly()->get_dict().begin()->first)]
            = 1 / base.get_univariate_poly()->get_dict().begin()->second;
        return pow(UnivariateExprPolynomial(univariate_polynomial(
                       base.get_univariate_poly()->get_var(), std::move(dict))),
                   -exp, prec);
    }
    if (exp == 0) {
        if (base == 0) {
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
    if (s.get_univariate_poly()->get_dict().count(deg) == 0)
        return Expression(0);
    else
        return (s.get_univariate_poly()->get_dict()).at(deg);
}

Expression UnivariateSeries::root(Expression &c, unsigned n)
{
    return pow_ex(c, 1 / Expression(n));
}

UnivariateExprPolynomial
UnivariateSeries::diff(const UnivariateExprPolynomial &s,
                       const UnivariateExprPolynomial &var)
{
    RCP<const Basic> p
        = s.get_univariate_poly()->diff(var.get_univariate_poly()->get_var());
    if (is_a<const UnivariatePolynomial>(*p))
        return UnivariateExprPolynomial(
            rcp_static_cast<const UnivariatePolynomial>(p));
    else
        throw std::runtime_error("Not a UnivariatePolynomial");
}

UnivariateExprPolynomial
UnivariateSeries::integrate(const UnivariateExprPolynomial &s,
                            const UnivariateExprPolynomial &var)
{
    map_int_Expr dict;
    for (auto &it : s.get_univariate_poly()->get_dict()) {
        if (it.first != -1) {
            dict.insert(std::pair<int, Expression>(it.first + 1,
                                                   it.second / (it.first + 1)));
        } else {
            throw std::runtime_error("Not Implemented");
        }
    }
    return UnivariateExprPolynomial(univariate_polynomial(
        var.get_univariate_poly()->get_var(), std::move(dict)));
}

UnivariateExprPolynomial
UnivariateSeries::subs(const UnivariateExprPolynomial &s,
                       const UnivariateExprPolynomial &var,
                       const UnivariateExprPolynomial &r, unsigned prec)
{
    UnivariateExprPolynomial result(
        r.get_univariate_poly()->get_var()->get_name());
    for (auto &i : s.get_univariate_poly()->get_dict())
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
