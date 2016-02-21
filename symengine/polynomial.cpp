#include <symengine/polynomial.h>
#include <symengine/add.h>
#include <symengine/mul.h>
#include <symengine/pow.h>
#include <symengine/constants.h>

namespace SymEngine {

UnivariatePolynomial::UnivariatePolynomial(const RCP<const Symbol> &var, const unsigned int &degree, map_uint_mpz&& dict) :
     degree_{degree}, var_{var}, dict_{std::move(dict)} {

    SYMENGINE_ASSERT(is_canonical(degree_, dict_))
}

UnivariatePolynomial::UnivariatePolynomial(const RCP<const Symbol> &var, const std::vector<mpz_class> &v) :
     var_{var} {

    for (unsigned int i = 0; i < v.size(); i++) {
        if (v[i] != 0)
            dict_add_term(dict_, v[i], i);
    }
    degree_ = v.size() - 1;

    SYMENGINE_ASSERT(is_canonical(degree_, dict_))
}

bool UnivariatePolynomial::is_canonical(const unsigned int &degree_, const map_uint_mpz& dict) const
{
    map_uint_mpz ordered(dict.begin(), dict.end());
    unsigned int prev_degree = (--ordered.end())->first;
    if (prev_degree != degree_)
        return false;

    return true;
}

std::size_t UnivariatePolynomial::__hash__() const
{
    std::hash<std::string> hash_string;
    std::size_t seed = UNIVARIATEPOLYNOMIAL;

    seed += hash_string(this->var_->get_name());
    for (const auto &it : this->dict_)
    {
        std::size_t temp = UNIVARIATEPOLYNOMIAL;
        hash_combine<unsigned int>(temp, it.first);
        hash_combine<long long int>(temp, it.second.get_si());
        seed += temp;
    }
    return seed;
}

bool UnivariatePolynomial::__eq__(const Basic &o) const
{
    if (eq(*var_, *(static_cast<const UnivariatePolynomial &>(o).var_)) and
        map_uint_mpz_eq(dict_, static_cast<const UnivariatePolynomial &>(o).dict_))
        return true;

    return false;
}

int UnivariatePolynomial::compare(const Basic &o) const
{
    const UnivariatePolynomial &s = static_cast<const UnivariatePolynomial &>(o);

    if (dict_.size() != s.dict_.size())
        return (dict_.size() < s.dict_.size()) ? -1 : 1;

    int cmp = var_->compare(*s.var_);
    if (cmp != 0)
        return cmp;

    return map_uint_mpz_compare(dict_, s.dict_);
}

RCP<const Basic> UnivariatePolynomial::from_dict(const RCP<const Symbol> &var, map_uint_mpz &&d)
{
    if (d.size() == 1) {
        if (d.begin()->first == 0)
            return integer(d.begin()->second);
        else if (d.begin()->first == 1) {
            if (d.begin()->second == 0)
                return zero;
            else if (d.begin()->second == 1)
                return var;
            else
                return Mul::from_dict(integer(d.begin()->second), {{var, one}});
        } else {
            if (d.begin()->second == 0)
                return zero;
            else if (d.begin()->second == 1)
                return pow(var, integer(d.begin()->first));
            else
                return Mul::from_dict(integer(d.begin()->second),
                    {{var, integer(d.begin()->first)}});
        }
    } else {
        return make_rcp<const UnivariatePolynomial>(var, (--(d.end()))->first, std::move(d));
    }
}

void UnivariatePolynomial::dict_add_term(map_uint_mpz &d, const mpz_class &coef, const unsigned int &n)
{
    auto it = d.find(n);
    if (it == d.end())
       d[n] = coef;
}

vec_basic UnivariatePolynomial::get_args() const {
    vec_basic args;
    for (const auto &p: dict_) {
        args.push_back(UnivariatePolynomial::from_dict(var_, {{p.first, p.second}}));
    }
    return args;
}

mpz_class UnivariatePolynomial::max_coef() const {
    mpz_class curr = dict_.begin()->second;
    for (const auto &it : dict_) {
        if (it.second > curr)
            curr = it.second;
    }
    return curr;
}

mpz_class UnivariatePolynomial::eval(const mpz_class &x) const {
    //TODO: Use Horner's Scheme
    mpz_class ans = 0;
    for (const auto &p : dict_) {
        mpz_class temp;
        mpz_pow_ui(temp.get_mpz_t(), x.get_mpz_t(), p.first);
        ans += p.second * temp;
    }
    return ans;
}

mpz_class UnivariatePolynomial::eval_bit(const int &x) const {
    //TODO: Use Horner's Scheme
    mpz_class ans = 0;
    for (const auto &p : dict_) {
        mpz_class temp = 1;
        temp <<= x * p.first;
        ans += p.second * temp;
    }
    return ans;
}

bool UnivariatePolynomial::is_zero() const {
    if (dict_.size() == 1 and dict_.begin()->second == 0)
        return true;
    return false;
}

bool UnivariatePolynomial::is_one() const {
    if (dict_.size() == 1 and dict_.begin()->second == 1 and
            dict_.begin()->first == 0)
        return true;
    return false;
}

bool UnivariatePolynomial::is_minus_one() const {
    if (dict_.size() == 1 and dict_.begin()->second == -1 and
            dict_.begin()->first == 0)
        return true;
    return false;
}

bool UnivariatePolynomial::is_integer() const {
    if (dict_.size() == 1 and dict_.begin()->first == 0)
        return true;
    return false;
}

bool UnivariatePolynomial::is_symbol() const {
    if (dict_.size() == 1 and dict_.begin()->first == 1 and
            dict_.begin()->second == 1)
        return true;
    return false;
}

bool UnivariatePolynomial::is_mul() const {
    if (dict_.size() == 1 and dict_.begin()->first != 0 and
            dict_.begin()->second != 1 and dict_.begin()->second != 0)
        return true;
    return false;
}

bool UnivariatePolynomial::is_pow() const {
    if (dict_.size() == 1 and dict_.begin()->second == 1 and
            dict_.begin()->first != 1 and dict_.begin()->first != 0)
        return true;
    return false;
}

/* UnivariateExprPolynomial::UnivariateExprPolynomial(const RCP<const Symbol> &var, const unsigned int &degree, map_uint_expr&& dict) :
     degree_{degree}, var_{var}, dict_{std::move(dict)} {

    SYMENGINE_ASSERT(is_canonical(degree_, dict_))
}

bool UnivariateExprPolynomial::is_canonical(const unsigned int &degree_, const map_uint_expr& dict) const
{
    map_uint_expr ordered(dict.begin(), dict.end());
    unsigned int prev_degree = (--ordered.end())->first;
    if (prev_degree != degree_)
        return false;

    return true;
}

std::size_t UnivariateExprPolynomial::__hash__() const
{
    std::hash<std::string> hash_string;
    std::size_t seed = UNIVARIATEEXPRPOLYNOMIAL;

    seed += hash_string(this->var_->get_name());
    for (const auto &it : this->dict_)
    {
        std::size_t temp = UNIVARIATEEXPRPOLYNOMIAL;
        hash_combine<unsigned int>(temp, it.first);
        hash_combine<Expression>(temp, it.second);
        seed += temp;
    }
    return seed;
}

bool UnivariateExprPolynomial::__eq__(const Basic &o) const
{
    if (eq(*var_, *(static_cast<const UnivariateExprPolynomial &>(o).var_)) and
        map_uint_mpz_eq(dict_, static_cast<const UnivariateExprPolynomial &>(o).dict_))
        return true;

    return false;
} */


RCP<const UnivariatePolynomial> add_uni_poly(const UnivariatePolynomial &a, const UnivariatePolynomial &b) {
    map_uint_mpz dict;
    for (const auto &it : a.dict_)
        dict[it.first] = it.second;
    for (const auto &it : b.dict_)
        dict[it.first] += it.second;

    RCP<const UnivariatePolynomial> c = univariate_polynomial(a.var_, (--(dict.end()))->first, std::move(dict));
    return c;
}

RCP<const UnivariatePolynomial> neg_uni_poly(const UnivariatePolynomial &a) {
    map_uint_mpz dict;
    for (const auto &it : a.dict_)
        dict[it.first] = -1 * it.second;

    RCP<const UnivariatePolynomial> c = univariate_polynomial(a.var_, (--(dict.end()))->first, std::move(dict));
    return c;
}

RCP<const UnivariatePolynomial> sub_uni_poly(const UnivariatePolynomial &a, const UnivariatePolynomial &b) {
    map_uint_mpz dict;
    for (const auto &it : a.dict_)
        dict[it.first] = it.second;
    for (const auto &it : b.dict_)
        dict[it.first] -= it.second;

    RCP<const UnivariatePolynomial> c = univariate_polynomial(a.var_, (--(dict.end()))->first, std::move(dict));
    return c;
}

//Calculates bit length of number, used in mul_uni_poly() only
template <typename T>
unsigned int bit_length(T t){
    unsigned int count = 0;
    while (t > 0) {
        count++;
        t = t >> 1;
    }
    return count;
}

RCP<const UnivariatePolynomial> mul_uni_poly(RCP<const UnivariatePolynomial> a, RCP<const UnivariatePolynomial> b) {
    //TODO: Use `const RCP<const UnivariatePolynomial> &a` for input arguments,
    //      even better is use `const UnivariatePolynomial &a`
    unsigned int da = a->degree_;
    unsigned int db = b->degree_;

    int sign = 1;
    if ((--(a->dict_.end()))->second < 0) {
        a = neg_uni_poly(*a);
        sign = -1 * sign;
    }
    if ((--(b->dict_.end()))->second < 0) {
        b = neg_uni_poly(*b);
        sign = -1 * sign;
    }

    mpz_class p = std::max(a->max_coef(), b->max_coef());
    unsigned int N = bit_length(std::min(da + 1, db + 1)) + bit_length(p) + 1;

    mpz_class a1 = 1 << N;
    mpz_class a2 = a1 / 2;
    mpz_class mask = a1 - 1;
    mpz_class sa = a->eval_bit(N);
    mpz_class sb = b->eval_bit(N);
    mpz_class r = sa*sb;

    std::vector<mpz_class> v;
    mpz_class carry = 0;

    while (r != 0 or carry != 0) {
        mpz_class b;
        mpz_and(b.get_mpz_t(), r.get_mpz_t(), mask.get_mpz_t());
        if (b < a2) {
            v.push_back(b + carry);
            carry = 0;
        } else {
            v.push_back(b - a1 + carry);
            carry = 1;
        }
        r >>= N;
    }

    if (sign == -1)
        return neg_uni_poly(*make_rcp<const UnivariatePolynomial>(a->var_, v));
    else
        return make_rcp<const UnivariatePolynomial>(a->var_, v);
}


  
///Multivariate Polynomial///

  
  
MultivariatePolynomial::MultivariatePolynomial( set_sym &vars, umap_sym_uint &degrees, umap_uvec_mpz &dict) :
   vars_{std::move(vars)}, degrees_{std::move(degrees)}, dict_{std::move(dict)} {
     SYMENGINE_ASSERT(is_cannonical(degrees_, dict_))
}

RCP<const Basic> MultivariatePolynomial::from_dict(set_sym &s, umap_uvec_mpz &&d){
  if(d.size() == 1){
    map_basic_basic b;
    int whichvar = 0;
    for(auto sym : s){
      b.insert( std::pair<RCP<const Basic>, RCP<const Basic>>(sym , make_rcp<Integer>(d.begin()->first[whichvar])) );
      whichvar++;
    }
    return Mul::from_dict(make_rcp<const Integer>(d.begin()->second), std::move(b));
  }
  else{
    umap_sym_uint degs;
    int whichvar = 0;
    for(auto sym : s){
      degs.insert(std::pair<RCP<const Symbol>, unsigned int>(sym,0));
      for(auto bucket : d){
	if(bucket.first[whichvar] > degs.find(sym)->second)
	  degs.find(sym)->second = bucket.first[whichvar];
      }
      whichvar++;
    }
    return make_rcp<const MultivariatePolynomial>(s,degs,d);
  }
}
  
vec_basic  MultivariatePolynomial::get_args() const{
  vec_basic args;
  for(const auto &p : dict_){
    args.push_back(MultivariatePolynomial::from_dict(vars_, {{p.first, p.second}}));
  }
  return args;
}
  
bool MultivariatePolynomial::is_canonical(set_sym &vars, umap_sym_uint &degrees, umap_uvec_mpz &dict){
    //checks that the maximum degree of any variable is correct according to the dictionary
    unsigned int whichvar = 0; //keeps track of the index of the variable we are checking
    for(auto var : vars){
        unsigned int maxdegree = 0;
        for(auto bucket : dict){
	  if(bucket.first[whichvar] > degrees.find(var)->second)
	        return false;
	  else if(maxdegree < bucket.first[whichvar] )
	    maxdegree = bucket.first[whichvar];
        }
        if(maxdegree != degrees.find(var)->second)
	    return false;
        whichvar++;
    }
    return true;
}

std::size_t MultivariatePolynomial::__hash__() const{
  std::hash<std::string> hash_string;
  std::size_t seed = 0;
  for(auto var : vars_)
    seed ^= hash_string(var->get_name()) + 0x9e3779b + (seed << 6) + (seed >> 2); //boost's method for combining hashes
  for(auto bucket : dict_){
    seed ^= vec_int_hash()(bucket.first) + 0x9e3779b + (seed << 6) + (seed >> 2);
    seed ^= mpz_hash(bucket.second) + 0x9e3779b + (seed << 6) + (seed >> 2);
  }
  return seed;
}

bool MultivariatePolynomial::__eq__(const Basic &o) const{
  
  return set_eq<RCP<const Symbol>>(vars_, rcp_static_cast<MultivariatePolynomial>(o)->vars_) && umap_eq<umap_vec_mpz>(dict_, rcp_static_cast<MultivariatePolynomial>(o)->dict_));
}

int MultivariatePolynomial::compare(const Basic &o) const{
  //copied from UnivariatePolynomial::compare and then modified.
    const MultivariatePolynomial &s = static_cast<const MultivariatePolynomial&>(o);
    
    if (dict_.size() != s.dict_.size())
        return (dict_.size() < s.dict_.size()) ? -1 : 1;

    int cmp = set_compare<RCP<const Symbol>>(vars_, s.vars_);
    if (cmp != 0)
        return cmp;

    return umap_vec_mpz_compare(dict_, s.dict_); 
}

mpz_class MultivariatePolynomial::eval(std::map<RCP<const Symbol>, mpz_class> &vals){
    mpz_class ans = 0;
    for (auto bucket : dict_) {
        mpz_class term = 1;
        unsigned int whichvar = 0;
        for(auto sym : vars_){
	  mpz_class temp;
	  mpz_pow_ui(temp.get_mpz_t(), vals.find(sym)->second, bucket.first[whichvar] );
	  term *= temp;
	  whichvar++;
      }
      ans += term;
    } 
    return ans;
}
/*
RCP<const MultivariatePolynomial> add_mult_poly(const MultivariatePolynomial &a, const MultivariatePolynomial &b){
}

RCP<const MultivariatePolynomial> neg_mult_poly(const MultivariatePolynomial &a){
}

RCP<const MultivariatePolynomial> sub_mult_poly(const MultivariatePolynomial &a, const MultivariatePolynomial &b){
}

RCP<const MultivariatePolynomial> mul_mult_poly(const MultivariatePolynomial &a, const MultivariatePolynomial &b){
}
*/
  
  
} // SymEngine
