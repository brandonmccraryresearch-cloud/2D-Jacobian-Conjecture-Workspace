-- M2 version of weight -4 block (generated from w4q.sing; a_i_j -> aiyj)
R = QQ[a2y2,a3y4,a4y6,a5y8,a6y10,a7y12,b3y3,b4y5,b5y7,b6y9,b7y11,b8y13,b9y15,b10y17,b11y19,b12y21,lam, MonomialOrder => GRevLex];
I = ideal((1)*1*1-lam,
  (3)*1*b3y3+(-2)*a2y2*1,
  (5)*1*b4y5+(-5)*a3y4*1,
  (7)*1*b5y7+(2)*a2y2*b4y5+(-3)*a3y4*b3y3+(-8)*a4y6*1,
  (9)*1*b6y9+(4)*a2y2*b5y7+(-1)*a3y4*b4y5+(-6)*a4y6*b3y3+(-11)*a5y8*1,
  (11)*1*b7y11+(6)*a2y2*b6y9+(1)*a3y4*b5y7+(-4)*a4y6*b4y5+(-9)*a5y8*b3y3+(-14)*a6y10*1,
  (13)*1*b8y13+(8)*a2y2*b7y11+(3)*a3y4*b6y9+(-2)*a4y6*b5y7+(-7)*a5y8*b4y5+(-12)*a6y10*b3y3+(-17)*a7y12*1,
  (15)*1*b9y15+(10)*a2y2*b8y13+(5)*a3y4*b7y11+(-5)*a5y8*b5y7+(-10)*a6y10*b4y5+(-15)*a7y12*b3y3+(-20)*1*1,
  (17)*1*b10y17+(12)*a2y2*b9y15+(7)*a3y4*b8y13+(2)*a4y6*b7y11+(-3)*a5y8*b6y9+(-8)*a6y10*b5y7+(-13)*a7y12*b4y5+(-18)*1*b3y3,
  (19)*1*b11y19+(14)*a2y2*b10y17+(9)*a3y4*b9y15+(4)*a4y6*b8y13+(-1)*a5y8*b7y11+(-6)*a6y10*b6y9+(-11)*a7y12*b5y7+(-16)*1*b4y5,
  (21)*1*b12y21+(16)*a2y2*b11y19+(11)*a3y4*b10y17+(6)*a4y6*b9y15+(1)*a5y8*b8y13+(-4)*a6y10*b7y11+(-9)*a7y12*b6y9+(-14)*1*b5y7,
  (18)*a2y2*b12y21+(13)*a3y4*b11y19+(8)*a4y6*b10y17+(3)*a5y8*b9y15+(-2)*a6y10*b8y13+(-7)*a7y12*b7y11+(-12)*1*b6y9,
  (15)*a3y4*b12y21+(10)*a4y6*b11y19+(5)*a5y8*b10y17+(-5)*a7y12*b8y13+(-10)*1*b7y11,
  (12)*a4y6*b12y21+(7)*a5y8*b11y19+(2)*a6y10*b10y17+(-3)*a7y12*b9y15+(-8)*1*b8y13,
  (9)*a5y8*b12y21+(4)*a6y10*b11y19+(-1)*a7y12*b10y17+(-6)*1*b9y15,
  (6)*a6y10*b12y21+(1)*a7y12*b11y19+(-4)*1*b10y17,
  (3)*a7y12*b12y21+(-2)*1*b11y19);
t0 = cpuTime();
G = gb I;
print("M2 over QQ: dim " | toString(dim I) | " degree " | toString(degree I) | " cpu " | toString(cpuTime() - t0));
"w4q_m2_gb.txt" << toString(gens G) << close;
exit 0;
