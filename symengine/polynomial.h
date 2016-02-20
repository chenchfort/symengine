/**
 *  \file polynomial.h
 *  Class for sparse Polynomial: UnivariatePolynomial and Polynomial
 **/
#ifndef SYMENGINE_POLYNOMIALS_H
#define SYMENGINE_POLYNOMIALS_H

#include <symengine/monomials.h>
#include <symengine/dict.h>
#include <symengine/basic.h>
#include <symengine/integer.h>
#include <symengine/symbol.h>
#include <symengine/expression.h>

namespace SymEngine {
//! UnivariatePolynomial Class
class UnivariatePolynomial : public Basic{
public:
    //! `degree` : Degree of UnivariatePolynomial
    //! `var_` : Variable of the uni-variate UnivariatePolynomial
    //! `dict_` : holds the UnivariatePolynomial
    // UnivariatePolynomial x**2 + 2*x + 1 has dict_ = {{0, 1}, {1, 2}, {2, 1}} with var_ = "x"
    unsigned int degree_;
    RCP<const Symbol> var_;
    map_uint_mpz dict_;
public:
    IMPLEMENT_TYPEID(UNIVARIATEPOLYNOMIAL)
    //! Constructor of UnivariatePolynomial class
    UnivariatePolynomial(const RCP<const Symbol> &var, const unsigned int &degree, map_uint_mpz&& dict);
    //! Constructor using a dense vector of mpz_class coefficients
    UnivariatePolynomial(const RCP<const Symbol> &var, const std::vector<mpz_class> &v);

    static RCP<const UnivariatePolynomial> create(const RCP<const Symbol> &var,
            const std::vector<mpz_class> &v) {
        return make_rcp<const UnivariatePolynomial>(var, v);
    }

    //! \return true if canonical
    bool is_canonical(const unsigned int &degree, const map_uint_mpz& dict) const;
    //! \return size of the hash
    std::size_t __hash__() const;
    /*! Equality comparator
     * \param o - Object to be compared with
     * \return whether the 2 objects are equal
     * */
    bool __eq__(const Basic &o) const;
    int compare(const Basic &o) const;

    /*! Creates appropriate instance (i.e Symbol, Integer,
    * Mul, Pow, UnivariatePolynomial) depending on the size of dictionary `d`.
    */
    static RCP<const Basic> from_dict(const RCP<const Symbol> &var, map_uint_mpz &&d);
    /*!
    * Adds coef*var_**n to the dict_
    */
    static void dict_add_term(map_uint_mpz &d,
            const mpz_class &coef, const unsigned int &n);
    mpz_class max_coef() const;
    //! Evaluates the UnivariatePolynomial at value x
    mpz_class eval(const mpz_class &x) const;
    //! Evaluates the UnivariatePolynomial at value 2**x
    mpz_class eval_bit(const int &x) const;

    //! \return `true` if `0`
    bool is_zero() const;
    //! \return `true` if `1`
    bool is_one() const;
    //! \return `true` if `-1`
    bool is_minus_one() const;
    //! \return `true` if integer
    bool is_integer() const;
    //! \return `true` if symbol
    bool is_symbol() const;
    //! \return `true` if mul
    bool is_mul() const;
    //! \return `true` if pow
    bool is_pow() const;

    virtual vec_basic get_args() const;

    inline RCP<const Symbol> get_var() const {
        return var_;
    }
    inline const map_uint_mpz& get_dict() const {
        return dict_;
    };

}; //UnivariatePolynomial

class UnivariateExprPolynomial: public Basic {
public:
    unsigned int degree_;
    RCP<const Symbol> var_;
    map_uint_expr dict_;
public:
    IMPLEMENT_TYPEID(UNIVARIATEEXPRPOLYNOMIAL)
    //! Constructor of UnivariatePolynomial class
    UnivariateExprPolynomial(const RCP<const Symbol> &var, const unsigned int &degree, map_uint_expr &&dict);
    //! Constructor using a dense vector of mpz_class coefficients
    UnivariateExprPolynomial(const RCP<const Symbol> &var, const std::vector<mpz_class> &v);
    static RCP<const UnivariateExprPolynomial> create(const RCP<const Symbol> &var,
            const std::vector<mpz_class> &v) {
        return make_rcp<const UnivariateExprPolynomial>(var, v);
    }

    bool is_canonical(const unsigned int &degree, const map_uint_expr & dict) const;
    
    std::size_t __hash__() const;
    /*! Equality comparator
     * \param o - Object to be compared with
     * \return whether the 2 objects are equal
     * */
    bool __eq__(const Basic &o) const;

    int compare(const Basic &o) const;

    //! Overload assignment operator
    RCP<const UnivariateExprPolynomial> &operator=(cons Expression &) = default;
    
    //! Overload assignment operator for reference
    RCP<const UnivariateExprPolynomial> &operator=(Expression &&other) SYMENGINE_NOEXCEPT
    {
        if (this != &other) {
            this->m_basic = std::move(other.m_basic);
        }
        return *this;
    }
    
    //! Destructor of Expression
    ~Expression() SYMENGINE_NOEXCEPT {}
    
    //! Overload stream operator
    friend std::ostream &operator<<(std::ostream &os, const UnivariateExprPolynomial &expr)
    {
        os << expr.m_basic->__str__();
        return os;
    }
    //! Overload addition
    friend Expression operator+(const Expression &a, const Expression &b)
    {
        return Expression(add(a.m_basic, b.m_basic));
    }
    //! Overload addition and assignment(+=)
    Expression &operator+=(const Expression &other)
    {
        m_basic = add(m_basic, other.m_basic);
        return *this;
    }
    //! Overload subtraction
    friend Expression operator-(const Expression &a, const Expression &b)
    {
        return Expression(sub(a.m_basic, b.m_basic));
    }
    //! Overload unary negative
    Expression operator-() const
    {
        Expression retval(*this);
        retval *= -1;
        return retval;
    }
    //! Overload subtraction and assignment(-=)
    Expression &operator-=(const Expression &other)
    {
        m_basic = sub(m_basic, other.m_basic);
        return *this;
    }
    //! Overload multiplication
    friend Expression operator*(const Expression &a, const Expression &b)
    
}; //UnivariateExprPolynomial

//! Adding two UnivariatePolynomial a and b
RCP<const UnivariatePolynomial> add_uni_poly(const UnivariatePolynomial &a, const UnivariatePolynomial &b);
//! Negative of a UnivariatePolynomial
RCP<const UnivariatePolynomial> neg_uni_poly(const UnivariatePolynomial &a);
//! Subtracting two UnivariatePolynomial a and b
RCP<const UnivariatePolynomial> sub_uni_poly(const UnivariatePolynomial &a, const UnivariatePolynomial &b);
//! Multiplying two UnivariatePolynomial a and b
RCP<const UnivariatePolynomial> mul_uni_poly(RCP<const UnivariatePolynomial> a, RCP<const UnivariatePolynomial> b);

inline RCP<const UnivariatePolynomial> univariate_polynomial(RCP<const Symbol> i, unsigned int deg, map_uint_mpz&& dict)
{
    return make_rcp<const UnivariatePolynomial>(i, deg, std::move(dict));
}

class sym_hash{
public:
  size_t operator()(const Symbol &s) const{
    return s.__hash__();
  }
};

class sym_compare{
  public:
  size_t operator()(const Symbol &a, const Symbol &b){
    return a.compare(b);
  }
};

class sym_eq{
 public:
  bool operator()(const Symbol &a, const Symbol &b){
    return a.__eq__(b);
  }
};

int umap_vec_mpz_compare(umap_vec_mpz &a, umap_vec_mpz &b){
  if(a.size() < b.size())
    return (a.size() < b.size()) ? -1 : 1;
  return 0;
};

 
 typedef std::set<Symbol, sym_compare> set_sym;
 typedef std::unordered_map<Symbol, unsigned int, sym_hash, sym_eq> umap_sym_uint;
 
 
 
class MultivariatePolynomial : public Basic{
public:
    //vars: set of variables for th polynomial
    //degrees: max degrees of the symbols
    //dict: dictionary for sparse represntation of polynomial, x**1 * y**2 + 3 * x**4 * y ** 5
    // is represented as {(1,2):1,(4,5):3}
    set_sym vars_;
    umap_sym_uint degrees_;
    umap_vec_mpz dict_;
public:
    //constructor from components
    MultivariatePolynomial(set_sym &var, umap_sym_uint degrees, umap_vec_mpz &dict);
    /*bool is_canonical(set_sym &vars, uamp_sym_uint &degrees, umap_vec_mpz &dict);
    std::size_t __hash__();
    bool __eq__(const Basic &o);
    int compare(const Basic &o);
    mpz_class eval(std::map<Symbol, mpz_class> &vals);*/   
};
/*
RCP<const MultivariatePolynomial> add_mult_poly(const MultivariatePolynomial &a, const MultivariatePolynomial &b);
RCP<const MultivariatePolynomial> neg_mult_poly(const MultivariatePolynomial &a);
RCP<const MultivariatePolynomial> sub_mult_poly(const MultivariatePolynomial &a, const MultivariatePolynomial &b);
RCP<const MultivariatePolynomial> mul_mult_poly(const MultivariatePolynomial &a, const MultivariatePolynomial &b);
*/
 

}  //SymEngine

#endif
