#set page(margin: (x: 1.5cm, y: 1.5cm))

= #align(center)[
#underline[Complex Analysis ]\
]

URL: https://www.youtube.com/playlist?list=PLMrJAkhIeNNQBRslPb7I0yTnES981R8Cg


== 4. Complex Logarithm \

$z&=x+i y \
  &= R [cos(theta)+i sin(theta)] \
  &= R e^(i theta)
$

$z=x+i y$ \
$w=u+i v$ \
$w = log(z)$

The inverse pair of $w$ is $z=e^(w)$. \

$z=e^(u+i v)&=e^u e^(i v) \
            &=e^u [cos(v)+i sin(v)]
$ 

By applying polar coordinate form:\

$R = e^u -> u = log(R) := log(abs(z))$\
$v = theta := angle z$

On the z-plane, the complex number of z is a point with multiple times of $2pi n$. However, on w-plane the complex logarithm of z, $w=log(z) $ can have infinite number of points on the line of $log(R)$.

$v=theta_p +2pi n:= angle z$ true for all integer n.

This idea comes down to as follows:\
$u=log(abs(z))$\
$v=theta_p + 2pi n$

$w &= u + i v \
   &= log(abs(z)) + i (theta_p+2pi n)$\

Replace $w$ as $log(z)$ then, \  

$log(z) = log(abs(z))+i(theta_p + 2pi n)$ for all integer n.

#image("complex analysis-01.svg")

== 5. Roots of Unity and Rational Powers of z

$log(z)=log(abs(z))+i(theta_p+2n pi) n in ZZ $\
$z^a$\
$z=e^(log(z)) => z^a = e^(a log(z))$

Rational $a=m/n in QQ subset RR quad m,n in ZZ$\

$Z^(m\/n) &= e^(m\/n log(Z))\
          &= e^(m/n log(R)+i m/n (theta_p + 2pi k))\
          &= e^(m/n log(R)) e^(i m/n theta_p) e^(i m/n 2pi k)
$

E.g. $root(4,16i)$\
$16i = 16 e^(i pi/2)$\
$16i^(1/4) &= 16^(1/4) e^(i pi/8) e^(i (2pi k)/4)\
&=2e^(i pi/8)e^(i pi/2 k)$\

#table(
  columns: 2,
  [*k*], [*k-th root*],
  [0], [$2e^(i pi/8)$],
  [1], [$2e^(i pi/8)e^(i pi/2) -> 2e^(i (5pi)/8)$],
  [2], [$2e^(i pi/8)e^(i pi) -> 2e^(i (9pi)/8)$],
  [3], [$2e^(i pi/8)e^(i (3pi)/2) -> 2e^(i (13pi)/8)$],
)

#image("complex analysis-02.svg", width: 60%)

== 6. Analytic Functions and Cauchy-Riemann Condition

Keyword: well-behaved, analytic function

#underline[Analytic Function]

A function $f(z)$ is #underline(stroke:black, text(fill: purple, weight: "bold")[analytic]) in a domain $DD subset CC$ if $f(z)$ is single valued and has a finite derivative $f prime (z)$ for every $Z in DD$. 

- Path Independent $->$ derivative must be same in any direction

#underline[Non Analytic Function]

$f(z)= overline(z)=x - i y -> $ no derivative exist!

$frac(d f,d z) &= limits(lim)_(Delta z -> 0) (f(z+ Delta z)- f(z))/(Delta z)\
&= limits(lim)_(Delta z ->0) overline(Delta Z)/(Delta Z)\
&= (Delta x - i Delta y)/(Delta x + i Delta y)$

Case 1. Approach $Delta z->0$ from real axis: $limits(lim)_(Delta x -> 0) (Delta x)/(Delta x) = 1$

Case 2. Approach $Delta z->0$ from imag axis: $limits(lim)_(Delta y -> 0) (-i Delta y)/(Delta y) = -1$

- Path Dependent

Examples of Analytic & Non-Analytic Functions

Analytic $f(z)$: Polynomial($z^n$), functions w/ Taylor series ($e^z, cos(z), sin(z), log(z), ...$)

Non-analytic $overline(z)$: cliff, cusp, ...

Cauchy-Riemann for Analytic function

- For a function to be analytic the derivative must be the same for the two paths on real & imag axes.

$f(z)=u(x,y)+i v(x,y)\
z = x + i y$

$frac(d f,d z) &= limits(lim)_(cases(Delta x -> 0,
Delta y -> 0)) (Delta u + i Delta v)/(Delta x + i Delta y)$

(1) Approach from real axis: $Delta y = 0$

$frac(d f,d z) &= limits(lim)_(Delta x -> 0) (Delta u + i Delta v)/(Delta x)
&= (partial u)/(partial x) + i (partial v)/(partial x)$

(2) Approach from imag axis: $Delta x = 0$

$frac(d f,d z) &= limits(lim)_(Delta y -> 0) (Delta u + i Delta v)/(i Delta y)\
&= (i(Delta u + i Delta v))/(i dot i Delta y)\
&=(Delta v - i Delta u)/(Delta y)\
&=(partial v)/(partial y) - i (partial u)/(partial y)$

As a result, the real part of (1) must be equal to real part of (2). The imag part of (1) must be equal to image part of (2).\
$ (partial u)/(partial x) &= (partial v)/(partial y),  (partial u)/(partial y) &= -(partial v)/(partial x) $

Furthermore, if a function $f(z)$ is analytic, the real and imag part satisfies Laplace's equation. \

$gradient^2 u = 0, gradient^2 v = 0 $
u and v are harmonic functions.

Example: Polynomial $Z^n$

$f(z)&=z^2\
&=(x+i y)^2\
&= x^2-y^2 + i 2x y ->$
$u = x^2-y^2,  v = 2x y$

(1) Real Axis

$(d f)/(d z) = (partial u)/(partial x) + i (partial v)/(partial x) = 2x + i 2y = 2z$

(2) Imag Axis

$(d f)/(d z) = (partial v)/(partial y) - i (partial u)/(partial y) = (partial 2x y)/(partial y) - i (partial (x^2-y^2))/(partial y)= 2x + i 2y i =  2z$

== 7. Analytic Functions Solve Laplace's Equation

Analytic Function:
- single valued function
- derivative exist (path independent)
- Real and Imag part satisfy Laplace Equation
- harmonic function

$f(z)=u(x,y)+i v(x,y), z=x+i y$

If $f(z)$ is analytic and u, v both twice differentiable, then \

(1) check $u$

$(partial u)/(partial x) = (partial v)/(partial y) =>  (partial)/(partial x) => (partial^2 u)/(partial x^2)=(partial^2 v)/(partial x partial y)\

(partial u)/(partial y) = -(partial v)/(partial x)=>  (partial)/(partial y) => 
(partial^2 u)/(partial y^2) = -(partial^2 v)/(partial x partial y)\

(partial^2 v)/(partial x partial y)=(partial^2 u)/(partial x^2), 

(partial^2 v)/(partial x partial y)=-(partial^2 u)/(partial y^2)\

(partial^2 u)/(partial x^2) = -(partial^2 u)/(partial y^2) => (partial^2 u)/(partial x^2) +(partial^2 u)/(partial y^2)=0 => gradient^2 u = 0
$

$u$ is a harmonic function!

(2) check $v$

$(partial u)/(partial x) = (partial v)/(partial y) =>  (partial)/(partial y) => (partial u)/(partial x partial y)=(partial^2 v)/(partial y^2)\

(partial u)/(partial y) = -(partial v)/(partial x)=>  (partial)/(partial x) => 
(partial^2 u)/(partial x partial y) = -(partial^2 v)/(partial x^2)\

(partial^2 u)/(partial x partial y)=(partial^2 v)/(partial x^2), 

(partial^2 u)/(partial x partial y)=-(partial^2 v)/(partial y^2)\

(partial^2 v)/(partial x^2) = -(partial^2 v)/(partial y^2) => (partial^2 v)/(partial x^2) +(partial^2 v)/(partial y^2)=0 => gradient^2 v = 0
$

$v$ is a harmonic function!

=== Cauchy-Riemann Condition in Polar Coordinates

$f(z)=u(R, theta) + i v(R,theta) "where" z = R e^(i theta)$

#underline[_Chain Rule Method_]

Total differential of z

$d z = (partial z)/(partial r) d r + (partial z)/(partial theta) d theta$


Radial Direction: if $theta$ is a constant ($theta$ not change), $d theta = 0$:

$d z = (partial z)/(partial r) d r -> (partial z)/(partial r) = (d z)/(d r) = d/(d r)r e^(i theta) = e^(i theta)$\
$(d z)/(d r) = e^(i theta) -> (d r)/(d z) = (1)/(e^(i theta))
$

$f prime(z) &= (partial f)/(partial r) (d r)/(d z)\
&=e^(-i theta) ((partial u)/(partial r)+i (partial v)/(partial r))$

Tangential Direction: if $r$ is a constant ($r$ not changed), $d r = 0$:

$d z = (partial z)/(partial theta) d theta -> (partial z)/(partial theta) = (d z)/(d theta) = d/(d theta)r e^(i theta) = r i e^(i theta)$

$(d z)/(d theta) = r i e^(i theta) -> (d theta)/(d z)&=(1)/(r i e^(i theta))\ &=(-i e^(-i theta))/(r)$

$f prime(z) &= (partial f)/(partial theta) (d theta)/(d z)\
&= (-i e^(-i theta))/(r)((partial u)/(partial theta)+i (partial v)/(partial theta))\
&=(e^(-i theta))/(r)(-i (partial u)/(partial theta)+(partial v)/(partial theta))$

Equate the two $f prime (z)$ in both directions:

$e^(-i theta) ((partial u)/(partial r)+i (partial v)/(partial r))=(e^(-i theta))/(r)(-i (partial u)/(partial theta)+(partial v)/(partial theta))$

Divide both sides by $e^(-i theta)$:

$(partial u)/(partial r)+i (partial v)/(partial r)&=(1)/(r)(-i (partial u)/(partial theta)+(partial v)/(partial theta))\
&=(1/r (partial v)/(partial theta)-i/r (partial u)/(partial theta))$

Finally, Cauchy-Riemann Equation as follows:

Real part: $(partial u)/(partial r) = 1/r (partial v)/(partial theta)$

Imag part: $(partial v)/(partial r) = -i/r (partial u)/(partial theta)$\

#underline[_Limit Method (ref. Gemini)_]

The standard definition of the complex derivative:

$f prime (z) = limits(lim)_(Delta z --> 0) (f(z+Delta z)-f(z))/(Delta z)$

For a complex function to be differentiable, this limit must be the same regardless of the direction in which $Delta z$ approaches to zero.

_Path 1. The radial limit: a small amount of change in radial direction at z $(Delta theta = 0)$_

- $z=r e^(i theta)$
- $z+Delta z &= (r+ Delta r)e^(i (theta+Delta theta))\
&=(r+ Delta r)e^(i theta)$

- $Delta z &= -r e^(i theta)+(r+ Delta r)e^(i theta)\
&=(-r+r+Delta r)e^(i theta)\
&= Delta r e^(i theta)
$

The limit becomes:

$f prime (z) &= limits(lim)_(Delta z --> 0) (f(z+Delta z)-f(z))/(Delta z)\
&= limits(lim)_(Delta r -> 0) (f((r+ Delta r)e^(i theta))-f(r e^(i theta)))/(Delta r e^(i theta))\
&=(1)/( e^(i theta)) [limits(lim)_(Delta r ->0) (f(r+ Delta r, theta)-f(r, theta))/(Delta r)]\
&=e^(-i theta) (partial f)/(partial r)\
&=e^(-i theta)((partial u)/(partial r)+(partial v)/(partial r)) 
$

_Path 2. The tangential limit $(Delta r = 0)$_

- $z=r e^(i theta)$
- $z+Delta z = r e^(i (theta+Delta theta))$

- $Delta z &= -z + r e^(i (theta+Delta theta))\
&= -r e^(i theta)+r e^(i (theta+Delta theta))\
&=-r e^(i theta)+r e^(i theta) dot e^(i Delta theta)\
&= (e^(i Delta theta)-1)r e^(i theta)
$

Using Taylor Series for $e^(i Delta theta)$:

$e^x = 1 + x + (x^2)/(2!)+(x^3)/(3!)+...$

$e^(i Delta theta) = 1 + (i Delta theta) + ((i Delta theta)^2)/(2!)+((i Delta theta)^3)/(3!)+...$

We can drop the higher terms as $Delta theta ->0$.

$e^(i Delta theta) approx 1 + i Delta theta$\

$Delta z &= (e^(i Delta theta)-1)r e^(i theta)\
&=(1 + i Delta theta -1)r e^(i theta)\
&=i r e^(i theta) Delta theta $

The limit becomes:

$f prime (z) &= limits(lim)_(Delta z --> 0) (f(z+Delta z)-f(z))/(Delta z)\
&= limits(lim)_(Delta theta -> 0) (f(r e^(i (theta+Delta theta)))-f(r e^(i theta)))/(i r e^(i theta) Delta theta)\
&=(1)/( i r e^(i theta)) [limits(lim)_(Delta theta ->0) (f(r, theta+Delta theta)-f(r, theta))/(Delta theta)]\
&=(1)/( i r e^(i theta)) (partial f)/(partial theta)\
&=(-i e^(-i theta))/(r)(partial f)/(partial theta)\
&=(-i e^(-i theta))/(r)((partial u)/(partial theta)+i (partial v)/(partial theta))\
&=e^(-i theta)/(r)(-i (partial u)/(partial theta)+(partial v)/(partial theta))$

If we equate the two $f prime (z)$ in both directions, we can get the same Cauchy-Riemann equation with Chain-Rule.

Verify that $log(z)$ is analytic away from $z=0$ using Cauchy-Riemann condition with polar form. 

$log(z)= log(R)+i theta\
u(R, theta)=log(R) \ v(R, theta)=theta$

Clearly, $u_theta=0$ because $u$ is a function of $R$ and $v_R$ is zero because v is a function of $theta$.

Real part: $(partial u)/(partial r) = 1/r (partial v)/(partial theta)$\

$(partial u)/(partial R)= 1/(partial R) log(R)=1/R$

$(partial v)/(partial theta)=1/(partial theta) theta=1$

$(partial u)/(partial R) = 1/r (partial v)/(partial theta)$ becomes $1/R = 1 1/R$

Imag part: $(partial v)/(partial r) = -i/r (partial u)/(partial theta)$\

$(partial v)/(partial R)=partial/(partial R) theta=0$

$(partial u)/(partial theta) = partial/(partial theta)R=0$


#underline[_Complex Functions(Analytic)_]

Theorem 1. A function $f(z)=u+i v$ that is\
- single valued, and
- has continuous $(partial u)/(partial x), (partial u )/(partial y),(partial v )/(partial x),(partial v )/(partial y)$
in a domain $DD subset CC$ is analytic in $DD$ _iff_ the Cauchy-Riemann conditions are satisfied at every point $z in DD$.

Theorem 2. If a $f(z)$ is analytic at $z$ then $f(z)$ has continuous derivatives of all orders! $f prime (z), f prime prime (z), ... f^(15)(z), ...$

The main application: $f(z)$ is analytic at $z_0$ _iff_ its Taylor series exists and converges to $f(z)$ in a neighborhood of $z_0$. 


== 8. Integrals in the Complex Plane (1/8/2025 Thu)

Given a function $f(z)=u(x,y)+i v(x,y) "where" z = x+ i y$ then\
$integral.cont f(z)= integral.cont (u+i v)(d x+i d x) = integral.cont [(u d x - v d y)+i(u d y + v d x)]$

_Cauchy-Goursat Theorem:_

If $f(z)$ is analytic inside a simple closed curve $C subset CC$ then $integral.cont f(z)d z = 0$.

By Green's Theorem:
$
integral.cont (P d x + Q d y) = limits(integral.double)_D (
    partial / (partial x) Q - partial / (partial y) P
) d A
$

$ integral.cont [(u d x - v d y)+i(u d y + v d x)] &= limits(integral.double)_(S) (-(partial u)/(partial x)-(partial v)/(partial y)) d x d y + limits(integral.double)_(S) ((partial u)/(partial x)-(partial v)/(partial y)) d x d y \ &=0
$

By Cauchy-Riemann conditions:

$ (partial u)/(partial x) &= (partial v)/(partial y) "and"  (partial u)/(partial y) &= -(partial v)/(partial x) $  

$ (partial u)/(partial x) - (partial v)/(partial y) = 0 "and" -(partial v)/(partial x) -(partial u)/(partial y) =0 $

Fundamental Theorem of Complex Calculus:
If $f$ is analytic in $DD$ and $z_0, z_1 in DD$ then,

$ limits(integral)_(z_0)^z_1 f(z) d z= F(z_1) - F(z_0) = 0 $

Integrals in the Complex Plance

Given a function $f(z)=u(x,y)+i v(x,y)$ then

$ limits(integral)_C f(z) d z &=  limits(integral)_C [(u d x - v d y)+i(u d y + v d x)] $

$ limits(integral)_(C_1) f(z)d z = limits(integral)_(C_2) f(z)d z $

$ limits(integral)_(C_1) f(z)d z-  limits(integral)_(C_2) f(z)d z = limits(integral)_(C_1) f(z)d z+  limits(integral)_(-C_2) f(z)d z = limits(integral.cont)_C f(z) d z =0 $

Fundamental Theorem Complex Calculus:

If $f$ is analytic in $DD$ and $z_0, z_1 in DD$ then,

$ limits(integral)_(z_0)^(z_1) = F(z_1)-F(z_0) $

Inside an analytic region $DD$, we can deform contours $C$ continuously and not change the value of integral. 

ML Bound: if $abs(f) <= M "on" C$ and length of that curve 
$ limits(integral)_C d x = L $ then
$ abs(limits(integral)_C f(z)d z) <= "ML" $

== 8. Complex Residues

All polynomials and all convergent Taylor series are all analytic inside Radius of convergence.

Functions w/ singularities are not analytic at singularities.

Ex: $ (z-a)^n "is" cases("analytic for" quad n=lr(0,1,2,dots), "non-analytic for" "at" z= a quad  n=lr(-1,-2,-3,dots)) $ 

Taylor series:
$ f(z) = limits(sum)_(n=0)^(infinity) C_n (z-a)^n $
Laurent series:
$ f(z) = limits(sum)_(n=-infinity)^(infinity) C_n (z-a)^n $

Case 1. $n=+1, +2, +3, ... "and n=-1, -2, -3, ..."$

$ limits(integral.cont)_C (z-a)^n d z = lr(((z-1)^(n+1))/(n+1) |)_(z_0)^(z_0) = 0 $

Case 2. $n=-1$

$ limits(integral.cont)_C (z-a)^(-1) d z = lr(log(z-a) |)_(z_0)^(z_1) = 2 pi i $

$ log(z) = log(R)+i(theta_p+2pi n) $

Circle w/ radius: $R$.

$z-a = R e^(i theta), d z = i R e^(i theta) d theta$

$ limits(integral.cont) (z-a)^(-1) d z &= limits(integral.cont) (1)/(R e^(i theta)) i R e^(i theta) d theta\
&= limits(integral.cont) i d theta\
&=2 pi i $

$ limits(integral.cont) (z-a)^n d z = cases(0 wide n != -1, 2 pi i wide n = -1) $

== 10. Cauchy Integral Formula (CIF)

If $f(z)$ is analytic inside and on a simple closed curve $C$, and if a point, 'a' inside $C$, then following integral formula is true.

$ limits(integral.cont)_C (f(z))/(z-a)d z = 2 pi i f(a) $

Proof.

$limits(integral.cont) (f(z))/(z-a) d z = limits(integral.cont) (f(a))/(z-a)d z + limits(integral.cont) (f(z)-f(a))/(z-a)d z$

$I_1 = limits(integral.cont) (f(a))/(z-a)d z \
I_2 = limits(integral.cont) (f(z)-f(a))/(z-a)d z$

Solve $I_1 ":" limits(integral.cont) (f(a))/(z-a)d z$

$f(a)$ is a constant, $f(a)$ can be placed outside the integral.

$ f(a) limits(integral.cont)1/(z-a)d z = f(a) 2 pi i $


Solve $I_2$

Deform contour $C$ into $C_s$. Shrink $C$. Everywhere is analytic except $a$. We can use Cauchy-Goursat Theorem. Shrink the couture $C$ very close to a. Since $f(z)$ is analytic around "a", we can choose $delta$ such that $abs(f(z)-a) < epsilon$. 

$ I_2 = limits(integral.cont)_(C_delta) (f(z)-f(a))/(z-a) d z => abs(I_2) <= limits(integral.cont) (epsilon)/(z-a) d z = 2 pi i epsilon =0 $

This is true for all $epsilon > 0$.

== 11. Examples of Cauchy-Integral Fromula

$diamond.filled$ $f(z)$ analytic inside and on closed curve $C$, and 'a' inside:

#align(left, block($ limits(integral.cont)_C (f(z))/(z-a)d z = 2 pi i f(a) $))

Example. $f(z) = 1/(z^2-3z+2) = 1/((z-a)(z-2))$ has poles at $z=1, 2$

Note $1/(z-1)$ is analytic at $z=2$ and $1/(z-1)$ is analytic at $z=1$

Consider four contours. $C_1$ around at $z=1$, $C_2$ around at $z=2$, $C_3$ including $z=1$ and $z=2$, and $C_4$ away from the singularities excluding $z=1$ and $z=2$.

Solve $C_1$:

#align(left, block($ limits(integral.cont)_(C_1) f(z)d z = limits(integral.cont)_(C_1)(1/(z-2))/(z-1) d z=-2 pi i wide because f(z)=1/(x-2) -> f(1)=-1 $))

Solve $C_2$:

#align(left, block($ limits(integral.cont)_(C_2) f(z)d z = limits(integral.cont)_(C_2)(1/(z-1))/(z-2) d z=2 pi i wide because f(z)=1/(x-1) -> f(2)=1 $))

Solve $C_3$:

If we draw a closed loop surrounding the singularities ($z=1,2$) in counter clock wise, the two paths going from $z=2$ to $z=1$ and vise versa cancel out. Therefore, the integral of $C_3$ will end up with the addition of the integral of $C_1$ and $C_2$. 

#align(left, block($ limits(integral.cont)_(C_3) f(z)d z &= limits(integral.cont)_(C_1) f(z) d z + limits(integral.cont)_(C_2) f(z)d z\
&=limits(integral.cont)_(C_1)(1/(z-2))/(z-1) d z+limits(integral.cont)_(C_2)(1/(z-1))/(z-2) d z\
&=-2pi i +2pi i\ &=0 $))

Solve $C_4$:

Everywhere is analytic in $C_4$. Therefore, the integral around $C_4$ is zero.

#align(left, block($ limits(integral.cont)_(C_4) f(z)d z = 0 $))

== 12. Examples of Complex Integrals

$limits(integral)_(-infinity)^(infinity) f(x) d x$ for real valued $f(x)$

Ex. $limits(integral)_0^infinity (d x)/(x^4+a^4) = 1/2 limits(integral)_(-infinity)^(infinity) (d x)/(x^4+a^4)$

$f(z)=1/(z^4+a^4)$ has poles at $z^4 = -a^4 -> z = a^4 sqrt((-1))$ 

Solving $z^4 = -a^4$ (Ref. Gemini)

To solve the equation, we first write the constant in polar form:
$ -a^4 = a^4 e^(i (pi + 2k pi)) $

Taking the fourth root of both sides:
$ z = (a^4 e^(i (pi + 2k pi)))^(1/4) = a e^(i (pi/4 + (k pi)/2)) $

For $k = 0, 1, 2, 3$, we find the roots:
$
z_k = a (cos(pi/4 + (k pi)/2) + i sin(pi/4 + (k pi)/2))
$

The four solutions are:
$
z_0, z_3 &= plus.minus a/sqrt(2) + i a/sqrt(2) \
z_1, z_2 &= plus.minus a/sqrt(2) - i a/sqrt(2)
$

Final compact form:
$ z = a/sqrt(2) (plus.minus 1 plus.minus i) $

#image("real value f(x).png", width: 40%)

If I take the limit goes to infinity, $C_1$ becomes $-infinity "to" +infinity$ and $C_R$ becomes $infinity$. Then the contribution of $limits(integral)_(C_R)$ becomes zero, and we can calculate $limits(integral)_(C_1)$ using Cauchy Integral Formula.


$ limits(integral.cont)_C = limits(integral)_(C_1)+limits(integral)_(C_R) wide => wide limits(integral.cont)_C f(z)d z = limits(integral)_(-R)^R (d x)/(x^4+a^4)+limits(integral)_(C_R) (d z)/(x^4+a^4) $

Factor out $z^4+a^4 = (z-a_1)(z-a_2)(z-a_3)(z-a_4)$

$ limits(integral.cont)_C f(z)d z = limits(integral.cont)_C (d z)/((z-a_1)(z-a_2)(z-a_3)(z-a_4)) $

Be aware of the property of the factors of $f(z)$ except at $z=a_1 "and" a_2$. Away from $z=a_1$ all others terms are analytic at $a_1$. Similarly, away from $z=a_2$, all others terms are analytic at $a_2$. We can use Cauchy Integral Formula. 

$ limits(integral.cont)_C (d z)/((z-a_1)(z-a_2)(z-a_3)(z-a_4)) &=limits(integral.cont)_(C_(a 1)) (1/((z-a_2)(z-a_3)(z-a_4)))/(z-a_1) + limits(integral.cont)_(C_(a 2)) (1/((z-a_1)(z-a_3)(z-a_4)))/(z-a_2) \
&= 2pi i (1)/((a_1-a_2)(a_1-a_3)(a_1-a_4)) + 2pi i (1)/((a_2-a_1)(a_2-a_3)(a_2-a_4))\
&=(2 pi i (a_3 + a_4 - a_1 - a_2))/((a_1-a_3)(a_1-a_4)(a_2-a_3)(a_2-a_4)) $$
$

Given the roots:
$ a_1 = a/sqrt(2)(1+i), quad a_2 = a/sqrt(2)(-1+i), quad a_3 = a/sqrt(2)(-1-i), quad a_4 = a/sqrt(2)(1-i) $

The numerator evaluates to:

$ a_1 + a_2 = a/sqrt(2)(1+i - 1+i) = a/sqrt(2)(2i) = (a i)/sqrt(2) $

$ a_3 + a_4 = a/sqrt(2)(-1-i + 1-i) = a/sqrt(2)(-2i) = -(a i)/sqrt(2) $

$ (a_3 + a_4) - (a_1 + a_2) = (-a i)/sqrt(2) - (a i)/sqrt(2) = (-2a i)/sqrt(2) $

$ 2pi i (a_3 + a_4 - a_1 - a_2) = 2pi i (-2a i sqrt(2)) = 4pi a sqrt(2) $

The denominator evaluates to:

$ (a_1 - a_3) = a/sqrt(2)(1+i - (-1-i)) = a/sqrt(2)(2+2i) = a sqrt(2)(1+i) $

$ (a_1 - a_4) = a/sqrt(2)(1+i - (1-i)) = a/sqrt(2)(2i) = a i sqrt(2) $

$ (a_2 - a_3) = a/sqrt(2)(-1+i - (-1-i)) = a/sqrt(2)(2i) = a i sqrt(2) $

$ (a_2 - a_4) = a/sqrt(2)(-1+i - (1-i)) = a/sqrt(2)(-2+2i) = a sqrt(2)(-1+i) $

$ (a_1-a_3)(a_1-a_4)(a_2-a_3)(a_2-a_4) &= a sqrt(2)(1+i)dot (a i)sqrt(2) dot (a i)sqrt(2) dot a sqrt(2)(-1+i)\
&= a^4 dot (sqrt(2))^4 dot i^2 dot (1+i) (-1+i)\
&=a^4 dot 4 dot (-1) dot (-1-1)\
&= 8a^4 $

Final result:
$ S = (4pi a sqrt(2)) / (8a^4) = (pi sqrt(2)) / (2a^3) $

If $R$ goes to $infinity$, $limits(integral.cont)_(C_R) (d z)/(z^4+a^4)$ goes to zero.

Proof:
$ limits(lim)_(R->infinity) limits(integral.cont)_(C_R) (d z)/(z^4+a^4) = 0 $

$ abs(limits(integral.cont)_(C_R) (d z)/(z^4+a^4)) <= "ML" "where" cases("L" = pi R, m=limits(max)_(C_R)1/(z^4+a^4)<=1/(R^4)) $

$ abs(limits(integral.cont)_(C_R) (d z)/(z^4+a^4))=pi/(R^4) -> 0 "where" R -> infinity $

Therefore,

$ limits(integral)_0^infinity (d x)/(x^4+a^4) &= 1/2 limits(integral)_(-infinity)^(infinity) (d x)/(x^4+a^4)\
&=1/2 (pi sqrt(2))/(2a^3)
$

== 13. Bromwich Integrals and the Inverse Laplace Transform
Laplace Transform: maps time domain to frequency domain. 

Inverse Laplace Transform: from freq to time.

$ L^(-1) {hat(f)(s)} eq.delta 1/(2pi i) limits(integral)_(gamma-i infinity)^(gamma+i infinity) hat(f) (s) e(s t) d s $ 
where $gamma > "real part of all poles of" hat(f)$

Why Laplace transform? To solve ODE and PDE(such as heat equation). Convert ODE to algebraic equation and solve. 

Specific example:
$hat(f) = 1/(s-a)$ 

$ L^(-1) {1/(s-a)} = 1/(2pi i) limits(integral)_(gamma-i infinity)^(gamma+i infinity) (e^(s t))/(s-a) d s $

#image("L13-fig-01.svg", width: 40%)

Using Cauchy Integral Formula.
$ 1/(2pi i) limits(integral.cont)_C (e^(s t))/(s-a) d s &= e^(a t) \
&= limits(integral.cont)_(C_1) + limits(integral.cont)_(C_+) + limits(integral.cont)_(C_-) + limits(integral.cont)_(C_R) $

if $R->infinity$, then 

$ limits(integral.cont)_(C_1) + limits(integral.cont)_(C_+) + limits(integral.cont)_(C_-) + limits(integral.cont)_(C_R) &= limits(integral.cont)_(C_1) + 0 + 0 + 0 \
&= e^(a t) $ 

$ limits(integral.cont)_(C_+) + limits(integral.cont)_(C_-) <- "use ML bound" $ Length is always $gamma = L$

$ limits(integral.cont)_(C_+) (e^(s t))/(s-a) d s= limits(integral)_(gamma-i infinity)^(gamma+i infinity) (e^(s t))/(s-a) d s = limits(integral)_(gamma)^(0) (e^(x+i R)t)/(x+i R-a) d x <= "ML" $

$ M=limits(max)_(x <= [0,gamma]) abs((e^((x+i R)t))/(x+i R -a )) <= (e^(gamma t))/R $

Numerator:

$ e^((x+i R)t) = e^(x t) dot e^(i R t) = e^(x t)(cos(R t)+i sin(R t)) $
$abs(e^((x+i R)t)) = e^(x t)sqrt(cos(R t)^2+sin(R t)^2)=e^(x t) -> x=gamma "then" e^(gamma t)$

Denominator:

$abs((x+i R -a )) = sqrt((x-a)^2+R^2) -> x=a "for smallest value" -> R$

Therefore,

$ M = (e^(gamma t))/R  wide L = gamma wide "when R" -> infinity, wide "ML"=(e^(gamma t))/R gamma -> 0 $ 

Solve for $limits(integral)_(C_R)$:

ML bound doesn't work for $C_R$. Try polar coordinate. 

*Step 4: Show the arc contribution vanishes (Ref: Claude)* 

On the semicircular arc in the left half-plane where $s = gamma + R e^(i theta)$ with $pi/2 <= theta <= (3pi)/2$:

$ |e^(s t)| = |e^((gamma + R e^(i theta))t)| = e^(gamma t) dot e^(R t cos theta) $

Since $cos theta < 0$ for $pi/2 < theta < (3pi)/2$, we have $e^(R t cos theta) -> 0$ as $R -> infinity$ for $t > 0$.

By Jordan's lemma, the contribution from the arc vanishes.




