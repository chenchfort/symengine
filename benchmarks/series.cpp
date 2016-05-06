#include <chrono>
#include <iostream>

#include <symengine/series_generic.h>
//#include <symengine/series_flint.h>
#include <flint/fmpz_mod_polyxx.h>

using SymEngine::Basic;
using SymEngine::Symbol;
using SymEngine::UnivariateSeries;
using SymEngine::symbol;
using SymEngine::map_vec_int;
using SymEngine::integer;
using SymEngine::integer_class;
using SymEngine::RCP;
using SymEngine::rcp_dynamic_cast;
using SymEngine::Expression;
using SymEngine::UnivariatePolynomial;
using SymEngine::UnivariateExprPolynomial;

int main(int argc, char *argv[])
{
    SymEngine::print_stack_on_segfault();

    RCP<const Symbol> x = symbol("x");
    std::vector<Expression> v;
    int N;
    flint::fmpz_polyxx xx, res;
    xx.set_coeff(3, 2);
    N = 100000;
    for (int i = 0; i < N; ++i) {
        Expression coef(i);
        v.push_back(coef);
        xx.set_coeff(i, i);
    }

    UnivariateExprPolynomial c, p(UnivariatePolynomial::create(x, v));
    /*auto t1 = std::chrono::high_resolution_clock::now();
    c = UnivariateSeries::mul3(p, p, 1000);
    auto t2 = std::chrono::high_resolution_clock::now();
    std::cout << std::chrono::duration_cast<std::chrono::milliseconds>(t2 - t1)
                     .count()
              << "ms" << std::endl;
    */
    /*auto t1 = std::chrono::high_resolution_clock::now();
    c = UnivariateSeries::mul(p, p, 1000);
    auto t2 = std::chrono::high_resolution_clock::now();
    std::cout << std::chrono::duration_cast<std::chrono::milliseconds>(t2 - t1)
                     .count()
              << "ms" << std::endl;
    */
    auto t1 = std::chrono::high_resolution_clock::now();
    res = mullow_SS(xx, xx, 100000);
    auto t2 = std::chrono::high_resolution_clock::now();
    std::cout << std::chrono::duration_cast<std::chrono::milliseconds>(t2 - t1)
                     .count()
              << "ms" << std::endl;
    
    //std::cout << res.pretty("x") << std::endl;
   /* auto arg = add(x, pow(x, integer(2)));
    auto arg = add(x, pow(x, integer(2)));
    auto ex = mul(sin(arg), cos(arg));
    std::cout << "Expanding: " << *ex << std::endl;

    t1 = std::chrono::high_resolution_clock::now();
    auto f = SymEngine::UnivariateSeries::series(ex, "x", N);
    t2 = std::chrono::high_resolution_clock::now();
    // std::cout << *res[N-1] << std::endl;
    std::cout << std::chrono::duration_cast<std::chrono::milliseconds>(t2 - t1)
                     .count()
              << "ms" << std::endl;
    */return 0;
}
