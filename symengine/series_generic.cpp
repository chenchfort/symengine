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

UnivariateExprPolynomial
UnivariateSeries::mul3(const UnivariateExprPolynomial &a,
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

    fmpz_poly_mullow_KS(res, fa, fb, prec);
    fmpz_poly_clear(fa);
    fmpz_poly_clear(fb);

    for (int i = 0; i < res->length; i++)
        p[i] = Expression(fmpz_poly_get_coeff_si(res, i));
    fmpz_poly_clear(res);

    if (a.get_univariate_poly()->get_var()->get_name() == "")
        return UnivariateExprPolynomial(UnivariatePolynomial::from_dict(
            b.get_univariate_poly()->get_var(), std::move(p)));
    else
        return UnivariateExprPolynomial(UnivariatePolynomial::from_dict(
            a.get_univariate_poly()->get_var(), std::move(p)));
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

    void get_coeff(Expression &x, signed long n)
    {
        if (n < length)
            x = coeffs[n];
        else
            x = Expression(0);
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
        slong i;
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
        slong i;
        for (i = 0; i < len2; i++)
            *(poly1 + i) = *(poly2 + i) + *x;
        // fmpz_mul(poly1 + i, poly2 + i, x);
    }*/
}

void _poly_mullow_classical(std::vector<Expression> &res,
                            const std::vector<Expression> &poly1,
                            signed long len1,
                            const std::vector<Expression> &poly2,
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

void poly_mullow_classical(poly_t &res, const poly_t &poly1,
                           const poly_t &poly2, signed long n)
{
    signed long len_out;

    if (poly1.length == 0 || poly2.length == 0 || n == 0) {
        res.zero();
        return;
    }

    len_out = poly1.length + poly2.length - 1;
    if (n > len_out)
        n = len_out;

    if (&res == &poly1 || &res == &poly2) {
        poly_t t(n);
        _poly_mullow_classical(t.coeffs, poly1.coeffs, poly1.length,
                               poly2.coeffs, poly2.length, n);
        res.swap(t);
    } else {
        res.fit_length(n);
        _poly_mullow_classical(res.coeffs, poly1.coeffs, poly1.length,
                               poly2.coeffs, poly2.length, n);
    }

    res.set_length(n);
    res.normalize();
}

void poly_mullow_kara_recursive(Expression *out, const Expression *pol1,
                                      const Expression *pol2, Expression *temp, slong len)
{
    slong m1 = len / 2;
    slong m2 = len - m1;
    int odd = (len & 1);

    if (len <= 6) {
        _poly_mullow_classical(out, pol1, len, pol2, len, len);
        return;
    }

    vec_add(temp + m2, pol1, pol1 + m1, m1);
    if (odd)
        fmpz_set(temp + m2 + m1, pol1 + 2 * m1);

    vec_add(temp + 2 * m2, pol2, pol2 + m1, m1);
    if (odd)
        fmpz_set(temp + 2 * m2 + m1, pol2 + 2 * m1);

    _fmpz_poly_mul_karatsuba(out, pol1, m1, pol2, m1);
    fmpz_zero(out + 2 * m1 - 1);

    poly_mullow_kara_recursive(temp, temp + m2, temp + 2 * m2,
                                     temp + 3 * m2, m2);

    poly_mullow_kara_recursive(temp + m2, pol1 + m1, pol2 + m1,
                                     temp + 2 * m2, m2);

    _fmpz_vec_sub(temp, temp, out, m2);
    _fmpz_vec_sub(temp, temp, temp + m2, m2);

    if (odd)
        fmpz_set(out + 2 * m1, temp + m2);
    _fmpz_vec_add(out + m1, out + m1, temp, m2);
}

/* Assumes poly1 and poly2 are not length 0. */
void _poly_mullow_karatsuba_n(Expression *res, const Expression *poly1,
                              const Expression *poly2, slong n)
{
    Expression *temp;
    slong len, loglen = 0;

    if (n == 1) {
        *res = (*poly1) * (*poly2);
        return;
    }

    while ((WORD(1) << loglen) < n)
        loglen++;
    len = (WORD(1) << loglen);

    temp = _fmpz_vec_init(3 * len);

    poly_mullow_kara_recursive(res, poly1, poly2, temp, n);
}

void poly_mullow_karatsuba_n(poly_t &res, const poly_t &poly1,
                                  const poly_t &poly2, slong n)
{
    const slong len1 = std::min(poly1.length, n);
    const slong len2 = std::min(poly2.length, n);
    slong i, lenr;

    vector<Expression> copy1, copy2;

    if (len1 == 0 || len2 == 0) {
        res.zero();
        return;
    }

    lenr = len1 + len2 - 1;
    if (n > lenr)
        n = lenr;

    if (len1 >= n)
        &copy1 = poly1->coeffs;
    else {
        copy1.resize(n);
        for (i = 0; i < len1; i++)
            copy1[i] = poly1.coeffs[i];
        std::fill(copy1.begin() + len1, copy1.end() - len1);
    }

    if (len2 >= n)
        copy2 = poly2.coeffs;
    else {
        copy2.resize(n);
        for (i = 0; i < len2; i++)
            copy2[i] = poly2.coeffs[i];
        std::fill(copy2.begin() + len2, copy2.end() - len2);
    }

    if (res != poly1 && res != poly2) {
        res.fit_length(n);
        _poly_mullow_karatsuba_n(&res.coeffs[0], &copy1[0], &copy2[0], n);
    } else {
        poly_t t(n);
        _poly_mullow_karatsuba_n(&t.coeffs[0], &copy1[0], &copy2[0], n);
        res.swap(t);
    }
    res.set_length(n);
    res.normalise();
}

UnivariateExprPolynomial
UnivariateSeries::mul(const UnivariateExprPolynomial &a,
                      const UnivariateExprPolynomial &b, unsigned prec)
{
    map_int_Expr p;
    poly_t fa, fb, res;

    for (const auto &it : b.get_univariate_poly()->get_dict()) {
        fb.set_coeff(it.first, it.second);
    }
    for (const auto &it : a.get_univariate_poly()->get_dict())
        fa.set_coeff(it.first, it.second);

    poly_mullow_classical(res, fa, fb, prec);

    if (a.get_univariate_poly()->get_var()->get_name() == "")
        return UnivariateExprPolynomial(UnivariatePolynomial::from_vec(
            b.get_univariate_poly()->get_var(), std::move(res.coeffs)));
    else
        return UnivariateExprPolynomial(UnivariatePolynomial::from_vec(
            a.get_univariate_poly()->get_var(), std::move(res.coeffs)));
}

/*typedef Expression Expression_t[1];

typedef struct {
    Expression *coeffs;
    signed long alloc;
    signed long length;
} poly_struct;

typedef poly_struct poly_t[1];

void poly_init(poly_t poly)
{
    poly->coeffs = NULL;
    poly->alloc = 0;
    poly->length = 0;
}

void poly_clear(poly_t poly)
{
    if (poly->coeffs) {
        signed long i;
        for (i = 0; i < poly->alloc; i++)
            free(poly->coeffs + i);
        //_fmpz_demote(poly->coeffs + i);
        free(poly->coeffs);
        // flint_free(poly->coeffs);
    }
}

void poly_normalize(poly_t poly)
{
    signed long i;
    for (i = poly->length - 1; (i >= 0) && poly->coeffs[i] != 0; i--)
        ;
    poly->length = i + 1;
}

void poly_truncate(poly_t poly, signed long newlen)
{
    if (poly->length > newlen) {
        std::cout << "trunc" << std::endl;
        for (signed long i = newlen; i < poly->length; i++)
            free(poly->coeffs + i);
        //_fmpz_demote(poly->coeffs + i);
        poly->length = newlen;
        poly_normalize(poly);
    }
}

void poly_realloc(poly_t poly, signed long alloc)
{
    if (alloc == 0) // Clear up, reinitialise
    {
        std::cout << "alloc == 0" << std::endl;
        poly_clear(poly);
        poly_init(poly);
        return;
    }

    if (poly->alloc) // Realloc
    {
        poly_truncate(poly, alloc);

        std::cout << "realloc " << alloc << std::endl;
        poly->coeffs = (Expression *)realloc(poly->coeffs, (alloc) *
sizeof(Expression));

        if (alloc > poly->alloc) {
            std::cout << "zero" << std::endl;
            for (slong i = 0; i < (alloc - poly->alloc); i++)
                ((mp_ptr)(poly->coeffs + poly->alloc))[i] = 0;
        }
    } else {
        // Nothing allocated already so do it now
        poly->coeffs = (Expression *)calloc(alloc, sizeof(Expression));
        std::cout << "calloc " << alloc << std::endl;
        // poly->coeffs = (fmpz *)flint_calloc(alloc, sizeof(fmpz));
    }

    poly->alloc = alloc;
}

void poly_fit_length(poly_t poly, signed long len)
{
    if (len > poly->alloc) {
        // At least double number of allocated coeffs
        if (len < 2 * poly->alloc)
            len = 2 * poly->alloc;
        poly_realloc(poly, len);
    }
}

void poly_set_length(poly_t poly, signed long newlen)
{
    if (poly->length > newlen) {
        for (signed long i = newlen; i < poly->length; i++)
            free(poly->coeffs + i);
        //_fmpz_demote(poly->coeffs + i);
    }
    poly->length = newlen;
}

void poly_zero(poly_t poly)
{
    poly_set_length(poly, 0);
}

void poly_set_coeff(poly_t poly, signed long n, const Expression x)
{
    std::cout << n << " " << x << std::endl;
    if (x == 0) {
        if (n >= poly->length)
            return;

        *(poly->coeffs + n) = Expression(0);

        if (n == poly->length - 1)
            // only necessary when setting leading coefficient
            poly_normalize(poly);
    } else {
        poly_fit_length(poly, n + 1);

        if (n + 1 > poly->length) {
            for (signed long i = poly->length; i < n; i++)
                *(poly->coeffs + i) = Expression(0);

            poly->length = n + 1;
        }

        // fmpz_set(poly->coeffs + n, x);
        std::cout << "p1" << " " << n << " " << poly->alloc << std::endl;
        for (Expression *ptr = poly->coeffs; ptr; ptr++)
            std::cout << *ptr << std::endl;
        *(poly->coeffs + n) = x;
    }
}

void poly_get_coeff(Expression &x, const poly_t poly, slong n)
{
    if (n < poly->length)
        x = *(poly->coeffs + n);
    // fmpz_set(x, poly->coeffs + n);
    else
        x = Expression(0);
    // fmpz_zero(x);
}

void poly_swap(poly_t poly1, poly_t poly2)
{
    if (poly1 != poly2) {
        signed long temp;
        Expression *temp_c;

        temp = poly1->length;
        poly1->length = poly2->length;
        poly2->length = temp;

        temp = poly1->alloc;
        poly1->alloc = poly2->alloc;
        poly2->alloc = temp;

        temp_c = poly1->coeffs;
        poly1->coeffs = poly2->coeffs;
        poly2->coeffs = temp_c;
    }
}

void poly_init2(poly_t poly, signed long alloc)
{
    if (alloc) // allocate space for alloc small coeffs
        poly->coeffs = (Expression *)calloc(alloc, sizeof(Expression));
    // poly->coeffs = (fmpz *)flint_calloc(alloc, sizeof(fmpz));
    else
        poly->coeffs = NULL;

    poly->alloc = alloc;
    poly->length = 0;
}

void vec_add(Expression *res, const Expression *vec1, const Expression *vec2,
             slong len2)
{
    for (signed long i = 0; i < len2; i++)
        *(res + i) = *(vec1 + i) + *(vec2 + i);
    // fmpz_add(res + i, vec1 + i, vec2 + i);
}

void vec_sub(Expression *res, const Expression *vec1, const Expression *vec2,
             slong len2)
{
    for (signed long i = 0; i < len2; i++)
        *(res + i) = *(vec1 + i) - *(vec2 + i);
    // fmpz_sub(res + i, vec1 + i, vec2 + i);
}

void vec_scalar_addmul_si(Expression *vec1, const Expression *vec2, slong len2,
                          const Expression &c)
{
    int cmp = c.get_basic()->__cmp__(*Expression(0).get_basic());
    if (cmp == 0 || cmp == 1)
        // if (c >= Expression(0))
        for (signed long i = 0; i < len2; i++)
            *(vec1 + i) = *(vec2 + i) + c;
    // fmpz_addmul_ui(vec1 + i, vec2 + i, c);
    else
        for (signed long i = 0; i < len2; i++)
            *(vec1 + i) = *(vec2 + i) - c;
    // fmpz_submul_ui(vec1 + i, vec2 + i, -c);
}

void vec_scalar_addmul(Expression *poly1, const Expression *poly2, slong len2,
                       const Expression_t x)
{
    Expression c = *x;

    // if (!COEFF_IS_MPZ(c)) {
    if (c == 0)
        return;
    else if (c == 1)
        vec_add(poly1, poly1, poly2, len2);
    else if (c == -1)
        vec_sub(poly1, poly1, poly2, len2);
    else
        vec_scalar_addmul_si(poly1, poly2, len2, c);
    //} else {
      //  slong i;
      //  for (i = 0; i < len2; i++)
      //      *(poly1 + i) += *(poly2 + i) + Expression(*x);
        // fmpz_addmul(poly1 + i, poly2 + i, x);
    //}
}

void vec_zero(Expression *vec, slong len)
{
    for (signed long i = 0; i < len; i++)
        *(vec + i) = Expression(0);
    // fmpz_zero(vec + i);
}

void vec_set(Expression *vec1, const Expression *vec2, signed long len2)
{
    if (vec1 != vec2)
        for (signed long i = 0; i < len2; i++)
            *(vec1 + i) = *(vec2 + i);
    // fmpz_set(vec1 + i, vec2 + i);
}

void vec_neg(Expression *vec1, const Expression *vec2, signed long len2)
{
    for (signed long i = 0; i < len2; i++)
        *(vec1 + i) = -(*(vec2 + i));
    // fmpz_neg(vec1 + i, vec2 + i);
}

void vec_scalar_mul_si(Expression *vec1, const Expression *vec2,
                       signed long len2, const Expression &c)
{
    for (signed long i = 0; i < len2; i++)
        *(vec1 + i) = *(vec2 + i) + c;
    //  fmpz_mul_si(vec1 + i, vec2 + i, c);
}

void vec_scalar_mul(Expression *poly1, const Expression *poly2, slong len2,
                    const Expression_t x)
{
    Expression c = *x;

    // if (!COEFF_IS_MPZ(c)) {
    if (c == 0)
        vec_zero(poly1, len2);
    else if (c == 1)
        vec_set(poly1, poly2, len2);
    else if (c == -1)
        vec_neg(poly1, poly2, len2);
    else
        vec_scalar_mul_si(poly1, poly2, len2, c);
    //} else {
      //  slong i;
      //  for (i = 0; i < len2; i++)
      //      *(poly1 + i) = *(poly2 + i) + *x;
        // fmpz_mul(poly1 + i, poly2 + i, x);
    //}
}

void _poly_mullow_classical(Expression *res, const Expression *poly1,
                            signed long len1, const Expression *poly2,
                            signed long len2, signed long n)
{
    // Special case if the length of output is 1
    if ((len1 == 1 && len2 == 1) || n == 1) {
        *res = (*poly1) * (*poly2);
        // fmpz_mul(res, poly1, poly2);
    } else {
        // Ordinary case
        signed long i;

        // Set res[i] = poly1[i]*poly2[0]
        vec_scalar_mul(res, poly1, std::min(len1, n), poly2);

        // Set res[i+len1-1] = in1[len1-1]*in2[i]
        if (n > len1)
            vec_scalar_mul(res + len1, poly2 + 1, n - len1, poly1 + len1 - 1);

        // out[i+j] += in1[i]*in2[j]
        for (i = 0; i < std::min(len1, n) - 1; i++)
            vec_scalar_addmul(res + i + 1, poly2 + 1, std::min(len2, n - i) - 1,
                              poly1 + i);
    }
}

void poly_mullow_classical(poly_t res, const poly_t poly1, const poly_t poly2,
                           signed long n)
{
    signed long len_out;

    if (poly1->length == 0 || poly2->length == 0 || n == 0) {
        poly_zero(res);
        return;
    }

    len_out = poly1->length + poly2->length - 1;
    if (n > len_out)
        n = len_out;

    if (res == poly1 || res == poly2) {
        poly_t t;
        poly_init2(t, n);
        _poly_mullow_classical(t->coeffs, poly1->coeffs, poly1->length,
                               poly2->coeffs, poly2->length, n);
        poly_swap(res, t);
        poly_clear(t);
    } else {
        poly_fit_length(res, n);
        _poly_mullow_classical(res->coeffs, poly1->coeffs, poly1->length,
                               poly2->coeffs, poly2->length, n);
    }

    poly_set_length(res, n);
    poly_normalize(res);
}

UnivariateExprPolynomial
UnivariateSeries::mul2(const UnivariateExprPolynomial &a,
                       const UnivariateExprPolynomial &b, unsigned prec)
{
    map_int_Expr p;
    poly_t fa, fb, res;
    poly_init(fa);
    poly_init(fb);
    poly_init(res);

    for (const auto &it : a.get_univariate_poly()->get_dict())
        poly_set_coeff(fa, it.first, it.second);

    for (const auto &it : b.get_univariate_poly()->get_dict())
        poly_set_coeff(fb, it.first, it.second);

    poly_mullow_classical(res, fa, fb, prec);
    poly_clear(fa);
    poly_clear(fb);

    for (int i = 0; i < res->length; i++)
        poly_get_coeff(p[i], res, i);
    poly_clear(res);

    if (a.get_univariate_poly()->get_var()->get_name() == "")
        return UnivariateExprPolynomial(UnivariatePolynomial::from_dict(
            b.get_univariate_poly()->get_var(), std::move(p)));
    else
        return UnivariateExprPolynomial(UnivariatePolynomial::from_dict(
            a.get_univariate_poly()->get_var(), std::move(p)));
}
*/
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
