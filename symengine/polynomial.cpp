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

MultivariatePolynomial::MultivariatePolynomial(const set_sym &vars, umap_sym_uint &degrees, umap_uvec_mpz &dict) :
vars_{std::move(vars)}, degrees_{std::move(degrees)}, dict_{std::move(dict)} {
    SYMENGINE_ASSERT(is_canonical(vars_, degrees_, dict_))
}

RCP<const Basic> MultivariatePolynomial::from_dict(const set_sym &s, umap_uvec_mpz &&d) const{
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
  
bool MultivariatePolynomial::is_canonical(const set_sym &vars, const umap_sym_uint &degrees, const umap_uvec_mpz &dict){
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
        seed ^= vec_uint_hash()(bucket.first) + 0x9e3779b + (seed << 6) + (seed >> 2);
        seed ^= mpz_hash(bucket.second) + 0x9e3779b + (seed << 6) + (seed >> 2);
    }
    return seed;
}

bool MultivariatePolynomial::__eq__(const Basic &o) const{
    return ( set_eq<set_sym>(vars_, static_cast<const MultivariatePolynomial &>(o).vars_) && umap_uvec_mpz_eq(dict_, static_cast<const MultivariatePolynomial &>(o).dict_) );
}

int MultivariatePolynomial::compare(const Basic &o) const{
    //copied from UnivariatePolynomial::compare and then modified.
    const MultivariatePolynomial &s = static_cast<const MultivariatePolynomial&>(o);
    
    if (dict_.size() != s.dict_.size())
        return (dict_.size() < s.dict_.size()) ? -1 : 1;

    int cmp = set_compare<set_sym>(vars_, s.vars_);
    if(cmp != 0)
        return cmp;

    return umap_uvec_mpz_compare(dict_, s.dict_); 
}

mpz_class MultivariatePolynomial::eval(std::map<RCP<const Symbol>, mpz_class, RCPSymbolCompare> &vals){
    mpz_class ans = 0;
    for(auto bucket : dict_) {
        mpz_class term = 1;
        unsigned int whichvar = 0;
        for(auto sym : vars_){
            mpz_class temp;
            mpz_pow_ui(temp.get_mpz_t(), vals.find(sym)->second.get_mpz_t(), bucket.first[whichvar] );
            term *= temp;
            whichvar++;
        }
        ans += term;
    } 
    return ans;
}

std::string MultivariatePolynomial::toString() const{
    std::ostringstream s;
    bool first = true; //is this the first term being printed out?
    std::vector<vec_uint> v;
    //To change the ordering in which the terms will print out, change
    //vec_uint_compare in dict.h
    for(auto bucket : dict_){
        auto it = v.begin();
	while(it != v.end() && vec_uint_compare()(bucket.first,*it)){
	    it++;
	}
	v.insert(it, bucket.first);
    }

    for(vec_uint exps : v){
        mpz_class c = dict_.find(exps)->second;
	if(c != 0){
	    if(c > 0 && !first)
    	        s << "+ ";
	    else if(c < 0)
	        s << "- "; 
            unsigned int i = 0;
	    std::ostringstream expr;
            for(auto it :vars_)
            {
   	        if(dict_.find(exps)->first[i] != 0)
   	            expr << it->get_name() << "**" << dict_.find(exps)->first[i] << " ";
	        i++;
            }
	    if(abs(c) != 1 || expr.str().empty())
	        s << abs(c);
	    s << expr.str();
	    first = false;
	}
    }
    
    if(s.str().empty())
        s << "0";
    return s.str();
}

unsigned int reconcile(vec_uint &v1, vec_uint &v2, set_sym &s, const set_sym &s1, const set_sym &s2){
    auto a1 = s1.begin();
    auto a2 = s2.begin();
    unsigned int poscount = 0;
    while(a1 != s1.end() && a2 != s2.end()){
        if(0 == (*a1)->compare(**a2) && (a1 != s1.end() && a2 != s2.end())){
            v1.insert(v1.end(), poscount);
	    v2.insert(v2.end(), poscount);
	    s.insert(*a1);
	    a1++;
	    a2++;
        } else if(-1 == (*a1)->compare(**a2)){
	    v1.insert(v1.end(),poscount);
            s.insert(*a1);
	    a1++;
        } else if(1 == (*a1)->compare(**a2)){
	    v2.insert(v2.end(),poscount);
	    s.insert(*a2);
	    a2++;
        }
	poscount++;
    }
    if(a1 == s1.end()){
        while(a2 != s2.end()){
	    v2.insert(v2.end(),poscount);
	    s.insert(*a2);
	    a2++;
	    poscount++;
        }
    } else if(a2 == s2.end()){
        while(a1 != s1.end()){
	    v1.insert(v1.end(),poscount);
            s.insert(*a1);
            a1++;
            poscount++;
        }
    }
    return poscount; //return size of the new vectors
}

vec_uint translate(vec_uint original, vec_uint translator, unsigned int size){
    vec_uint changed;
    for(unsigned int i = 0; i < size; i++){
        changed.insert(changed.end(), 0);
    }
    for(unsigned int i = 0; i < original.size(); i++){
        changed[translator[i]] = original[i];
    }
    return changed;
}

unsigned int max(unsigned int a, unsigned int b){
  return a < b ? b : a;
}

RCP<const MultivariatePolynomial> add_mult_poly(const MultivariatePolynomial &a, const MultivariatePolynomial &b){
    vec_uint v1;
    vec_uint v2;
    set_sym s;
    umap_uvec_mpz dict;
    umap_sym_uint degs;
    unsigned int size = reconcile(v1,v2,s,a.vars_,b.vars_);
    for(auto bucket : a.dict_){
        dict.insert(std::pair<vec_uint, mpz_class>(translate(bucket.first,v1,size), bucket.second)); 
    }
    for(auto bucket : b.dict_){
        auto target = dict.find(translate(bucket.first,v2,size));
        if(target != dict.end()){
            target->second += bucket.second;
        } else{
            dict.insert(std::pair<vec_uint, mpz_class>(translate(bucket.first,v2,size),bucket.second));
        }
    }
    for(auto bucket : s){
      degs.insert(std::pair<RCP<const Symbol>, unsigned int>(bucket, max(a.degrees_.find(bucket)->second, b.degrees_.find(bucket)->second)));
    }
    return make_rcp<const MultivariatePolynomial>(s,degs ,dict);
}

// adds together translate two vec_uints to the proper format and adds them together componentwise 
vec_uint uint_vec_translate_and_add(const vec_uint &v1, const vec_uint &v2,const vec_uint &translator1, const vec_uint &translator2, const unsigned int size){
    vec_uint result;
    for(unsigned int i = 0; i < size; i++){
        result.insert(result.end(), 0);
    }
    for(unsigned int i = 0; i < translator1.size(); i++){
        result[translator1[i]] += v1[i];
    }
    for(unsigned int i = 0; i < translator2.size(); i++){
        result[translator2[i]] += v2[i];
    }
    return result;
}

RCP<const MultivariatePolynomial> neg_mult_poly(const MultivariatePolynomial &a){
    umap_uvec_mpz dict;
    set_sym s = a.vars_;
    umap_sym_uint degs =a.degrees_;
    for(auto bucket : a.dict_){
        dict.insert(std::pair<vec_uint, mpz_class>(bucket.first, - bucket.second));
    }
    return make_rcp<const MultivariatePolynomial>(s, degs, dict);
}

RCP<const MultivariatePolynomial> sub_mult_poly(const MultivariatePolynomial &a, const MultivariatePolynomial &b){
    return(add_mult_poly(a, *neg_mult_poly(b)));
}

RCP<const MultivariatePolynomial> mul_mult_poly(const MultivariatePolynomial &a, const MultivariatePolynomial &b){
    vec_uint v1;
    vec_uint v2;
    set_sym s;
    umap_uvec_mpz dict;
    umap_sym_uint degs;
    unsigned int size = reconcile(v1,v2,s,a.vars_,b.vars_);
    for(auto bucket : s){
        degs.insert(std::pair<RCP<const Symbol>, unsigned int>(bucket,a.degrees_.find(bucket)->second + b.degrees_.find(bucket)->second));
    }
    for(auto a_bucket : a.dict_){
        for(auto b_bucket : b.dict_){
            dict.insert(std::pair<vec_uint, mpz_class>(uint_vec_translate_and_add(a_bucket.first,b_bucket.first,v1,v2,size), a_bucket.second * b_bucket.second));
        }
    }
    return make_rcp<const MultivariatePolynomial>(s, degs, dict);    
}
  
  
} // SymEngine
