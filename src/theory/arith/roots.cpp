#include "theory/arith/roots.h"
#include <boost/math/special_functions/fpclassify.hpp>

#include <math.h>

using namespace std;

namespace CVC4 {
namespace theory {
namespace arith {

Rational initialGuess(const Rational& q, unsigned long int n);
void setMin(Rational& min, const Rational& x);
void setMax(Rational& max, const Rational& x);


std::pair<Integer, Integer> rootRem(const Integer& u, unsigned long int n){
  CheckArgument(u.sgn() >= 0, this,
                "Negative integer passed to Integer::perfectRoot()");
  CheckArgument(n > 0, this,
                "Zero passed as n into Integer::perfectRoot()");

  if(u.sgn() == 0){
    return std::make_pair(Integer(0), Integer(0));
  }

  // https://gmplib.org/manual/Nth-Root-Algorithm.html

  int rounds = 0;
  
  Integer xp;
  Integer x = initialGuess(u, n).ceiling();
  do {
    rounds++;
    
    xp = x;
    Integer xp_n1 = xp.pow(n-1);
    x = (Integer(n-1)*xp + xp_n1).floorDivideQuotient(n);
    Debug("rootRem") << "rootRem("<<u<< ", " << n<<") round #"<<rounds
                     << xp << " -> " << x << std::endl;
  } while( (x - xp).abs() > 1 );

  Integer rem = u - x.pow(n);
  while(rem.sgn() < 0){
    Debug("rootRem") << "rootRem("<<u<< ", " << n<<") refine rem"
                     << rem << " x" << x << " x^n " << x.pow(n) << " u " << u  << endl;
    x = x - 1;
    rem = u - x.pow(n);
    
  }
  
  Debug("rootRem") << "rootRem("<<u<< ", " << n<<") return"
                   << "<" << x << ", " << rem << ">" << std::endl;
  return make_pair(x, rem);
}

// Integer initialGuess(const Integer& u, unsigned long int n){
//   CheckArgument(u.sgn() > 0, this,
//                 "Non-positive integer passed to Integer::perfectRoot()");
//   CheckArgument(n > 0, this,
//                 "Zero passed as n into Integer::perfectRoot()");

//   // x_0 = 2**ceil( ceil(log2(A)) / n)
//   size_t logS = u.length(); // ceil(log2(A))
//   unsigned long int log = ((unsigned long int) logS);
//   if(log < logS){
//     // Does this even matter?
//     log = std::numeric_limits<unsigned long int>::max();
//   }

//   unsigned long int divN = log / n;   //
//   // an overflow cannot happen as if n > 1, divN < floor(log/2)
//   Assert((log % n != 0) || divN < divN + 1);
//   unsigned long int ceilDiv = divN + ((log % n == 0) ? 0 : 1);

//   return Integer(1).multiplyByPow2(ceilDiv);
// }


std::pair<Rational, Rational> estimateNthRoot(const Rational& q, unsigned long int n, const Rational& D)
{
  CheckArgument(q.sgn() >= 0, this,
                "Negative integer passed to Integer::perfectRoot()");
  CheckArgument(n > 0, this,
                "Zero passed as n into Integer::perfectRoot()");
  CheckArgument(D.sgn() > 0, this,
                "Zero passed as n into Integer::perfectRoot()");

  if(q.sgn() == 0){
    return std::make_pair(Integer(0), Integer(0));
  }

  // https://gmplib.org/manual/Nth-Root-Algorithm.html

  int rounds = 0;

  Rational n_minus_1(n-1);
  Rational one_over_n((long unsigned)1, n);

  Rational lower(0);
  Rational upper;

  if(q <= 1){
    upper = Rational(1);
  }else{
    upper = q;
  }
  
  Rational xp;
  Rational x = initialGuess(q, n);
  Rational rem;
  Rational xp_to_n1 = x.pow(n-1);
  do {
    rounds++;
    
    xp = x;
    Assert(xp.pow(n-1) == xp_to_n1);
    x = (n_minus_1 * xp + q / xp_to_n1) * one_over_n;
    // x^{n-1}
    Debug("rootRem") << "rootRem(" << q << ", " << n <<") round #" << rounds
                     << " " << xp << " -> " << x << std::endl;

    xp_to_n1 = x.pow(n-1);
    rem = q - (x*xp_to_n1); // u - x**n

    if(rem.sgn() < 0){ // u < x**n
      setMin(upper, x);
    }else if(rem.sgn() > 0){ // u > x**n
      setMax(lower, x);
    }
  } while( rem.abs() > D );
  Assert((q-x.pow(n)).abs() <= D);
  

  Debug("rootRem") << "(|rem| <= D) : |" << rem << "| <= " << D << std::endl;
  Debug("rootRem") << "rootRem(" << q << ", " << n <<") round #" << rounds
                   << " lower " << lower
                   << " x " << x
                   << " upper " << upper
                   << std::endl;

  int deriv = rem.sgn();

  // |q - (x**n)| <= D
  if(deriv == 0){
    lower = x;
    upper = x;
  } else if(deriv > 0){
    // u - (x**n) > 0
    // (x**n) < u
    // |u - (x**n)| = u - (x**n) <= D
    // u <= (x**n) + D
    Assert(lower == x);
    Assert(deriv == 1);
  } else {
    // u - (x**n) < 0
    // (x**n) > u
    // |u - (x**n)| = - (u - (x**n)) <= D
    // (x**n) -D <= u
    Assert(upper == x);
    Assert(deriv == -1);
  }

  int jumpRounds = 0;
  Rational base = D * Integer(deriv);
  while( deriv * rem.sgn() > 0){
    jumpRounds++;
    x = x + base;
    base = base * 2;
    rem = q-x.pow(n);

    if(rem.sgn() < 0){ // u < x**n
      setMin(upper, x);
    }else if(rem.sgn() > 0){ // u > x**n
      setMax(lower, x);
    }else{
      lower = x;
      upper = x;
    }


    Debug("rootRem") << "jump(" << q << ", " << n <<") round #" << jumpRounds
                     << " lower " << lower
                     << " x " <<x
                     << " upper " << upper
                     << "rem " << rem
                     << "deriv " << deriv
                     << endl;
  }


  Debug("rootRem") << "rootRem(" << q << ", " << n <<") round #" << rounds
                   << " lower " << lower
                   << " x " <<x
                   << " upper " << upper
                   << std::endl;

  // refine by bisection
  
  Assert(lower <= upper);
  Assert(lower.pow(n) <= q);
  Assert(q <= upper.pow(n));

  Rational diff = upper - lower;
  while(diff >= D){
    Rational mid = (upper + lower)/2;
    Rational midPow = mid.pow(n);
    rem = q - midPow;

    Debug("rootRem") << "bisect"
                     << " q " << q
                     << " mid " << mid
                     << " midPow " << midPow
                     << " rem " << rem
                     << " lower " << lower
                     << "  " <<x
                     << " upper " << upper
                     << std::endl;

    Assert(lower < mid && mid < upper);
    if(rem.sgn() == 0){
      lower = mid;
      upper = mid;
    }else if(rem.sgn() < 0){
      // u - mid**n < 0
      upper = mid;
    }else{ // rq - midPow > 0
      // q > midPow
      lower = mid;
    }
    diff = upper - lower;
  }


  Assert(lower <= upper);
  Assert(lower.pow(n) <= q);
  Assert(q <= upper.pow(n));

  Debug("rootRem") << "final rootRem(" << q << ", " << n <<")"
                   << " lower " << lower
                   << " upper " << upper
                   << std::endl;
  return make_pair(lower, upper);
}

Rational initialGuess(const Rational& q, unsigned long int n){
  CheckArgument(q.sgn() > 0, this,
                "Non-positive integer passed to Integer::perfectRoot()");
  CheckArgument(n > 0, this,
                "Zero passed as n into Integer::perfectRoot()");


  // Try to get near: 2**(log2(q)/ n) 
  double qDouble = q.getDouble();
  if(boost::math::isnormal(qDouble) && qDouble > 0.0 ){
    Assert(qDouble > 0.0);
    double pow = log(qDouble)/((double)n);
    double res = exp(pow);
    try{
      Rational fd = Rational::fromDouble(res);
      return fd;
    }catch(RationalFromDoubleException&){
      // fall through on failure
    }
    // fall through on failure
  }else{
    // fall through in this case
  }

  // Guess as if it was an integer.
  // x_0 = 2**ceil( ceil(log2(ceiling(q))) / n)
  size_t logS = (q.ceiling()).length(); // ceil(log2(ceiling(q)))
  unsigned long int log = ((unsigned long int) logS);
  if(log < logS){
    // Does this even matter?
    log = std::numeric_limits<unsigned long int>::max();
  }

  unsigned long int divN = log / n;   //
  // an overflow cannot happen as if n > 1, divN < floor(log/2)
  Assert((log % n != 0) || divN < divN + 1);
  unsigned long int ceilDiv = divN + ((log % n == 0) ? 0 : 1);

  Integer intGuess = Integer(1).multiplyByPow2(ceilDiv);
  return intGuess;
}

void setMin(Rational& min, const Rational& x){
  if(x < min){
    min = x;
  }
}

void setMax(Rational& max, const Rational& x){
  if(x > max){
    max = x;
  }
}

}/* CVC4::theory::arith namespace */
}/* CVC4::theory namespace */
}/* CVC4 namespace */
