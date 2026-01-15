#box(
raw(  
"octave
z = 2 + 1i
R = abs(z)
th_p = atan2(1,2)
n = 8
nn = linspace(-pi*n/2, pi*n/2, n)
u = R
v = th_p*nn
subplot(1,3,1)
plot([0,real(z)], [0, imag(z)], '-')

subplot(1,3,2)
plot(u,v,'x','markersize', 10, 'markerfacecolor', 'r', 'markeredgecolor', 'r')

nth = 80
th_i = linspace(-2*pi, 2*pi, nth)
xx = R*cos(th_i)
yy = R*sin(th_i)
zz = th_i

subplot(1,3,3)
plot3(xx,yy,zz)
"
,
lang: "octave",
),
inset: 8pt,
stroke: 1pt
)